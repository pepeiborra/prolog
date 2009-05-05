
{-# LANGUAGE NoMonomorphismRestriction, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

-- | This is a simple Prolog evaluator written just for fun.
--   It does not support anything apart from basic Logic Programming,
--   i.e. no Cut, no arithmetic, no E/S.

module Language.Prolog.Semantics -- (eval, debug, unify, zonk, Environment, MonadFresh(..))
   where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM, zipWithM, zipWithM_, msum, MonadPlus(..), join, ap, (>=>))
import Control.Monad.Free hiding (mapM)
import Control.Monad.Free.Zip
import Control.Monad.RWS (RWS, RWST)
import Control.Monad.State  (State, StateT(..), MonadState(..), execStateT, evalState, evalStateT, modify, MonadTrans(..))
import Control.Monad.Writer (WriterT(..), MonadWriter(..), execWriterT)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Foldable (foldMap, toList, Foldable)
import Data.Monoid
import Data.Traversable as T
import Data.Map (Map)
import Text.PrettyPrint

import Prelude hiding (mapM)

import Debug.Trace

import Language.Prolog.Syntax

newtype Environment termF var = Env {unEnv::Map var (Free termF var)}
  deriving Monoid
liftEnv f (Env e) = Env (f e)

deriving instance Ord VName

instance (Ppr var, Ppr (Free termF var)) => Ppr (Environment termF var) where
    ppr = braces . hcat . punctuate comma . map (\(v,t) -> ppr v <+> equals <+> ppr t) . Map.toList . unEnv

restrictTo :: Ord var => [var] -> Environment id var -> Environment id var
restrictTo vv = liftEnv f where
  f e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

eval  :: (Ppr id, Ppr idp, Eq id, Eq idp, term ~ Term' id VName) => Program'' idp term -> GoalF idp term -> [Environment (TermF id) VName]
eval pgm q = (fmap (restrictTo (snub $ foldMap vars q) .  zonkEnv . snd) . execEnvM' i . runWriterT . run pgm) q
    where zonkEnv env = liftEnv (\m -> head $ evalEnvM env (mapM zonk m)) env
          i = maximum [ i | Auto i <- foldMap vars q] + 1

debug :: (Eq idp, Ppr id, Ppr idp, Eq id, term ~ Term' id VName) => Program'' idp term -> GoalF idp term -> [ [[GoalF idp term]] ]
debug pgm q =  ((`evalStateT` (Sum i, mempty)) . unEnvM . execWriterT . run pgm) q
  where
    i = maximum [ i | Auto i <- foldMap vars q] + 1
--run :: (Eq id, Ppr id, Ppr idp, Eq idp, term ~ Term' id var, var ~ VName, MonadPlus m, MonadFresh id var m, MonadEnv id var m, MonadWriter [[GoalF idp term]] m) => Program'' idp term -> Goal idp term -> m ()
run pgm query = go [query] where
  go []         = return ()
  go (Cut:rest) = go rest
  go prob@(goal:rest) = do
        mapM2 zonk prob >>= \prob' -> tell [prob']
        head :- body <- liftList pgm >>= freshInstance
        unify goal head
        go (body ++ rest)

  freshInstance c = getEnv >>= \env -> evalStateT (mapM2 (lift . fresh) c) (mempty `asTypeOf` env)

-- Unification
-- -----------
class (Functor termF, Eq var) => Unify termF var t | t -> termF var where unify :: MonadEnv termF var m => t -> t -> m ()
instance (Unify termF var (Free termF var), Eq idp, Foldable termF) => Unify termF var (GoalF idp (Free termF var)) where
  unify (Pred ft t) (Pred fs s) | ft /= fs = fail "Can't unify"
  unify (Pred ft t) (Pred fs s) = zipWithM_ unify t s

-- Generic instance
instance (Functor f, Foldable f, Eq var, Eq (f ())) => Unify f var (Free f var) where
  unify = unifyF where
   unifyF t s = do
    t' <- find t
    s' <- find s
    case (t', s') of
      (Pure vt, Pure vs) -> if vt /= vs then varBind vt s' else return ()
      (Pure vt, _)  -> if vt `Set.member` Set.fromList (vars s') then fail "occurs" else varBind vt s'
      (_, Pure vs)  -> if vs `Set.member` Set.fromList (vars t') then fail "occurs" else varBind vs t'
      (Impure t, Impure s)
        | (const () <$> t) == (const () <$> s) -> zipWithM_ unifyF (toList t) (toList s)
        | otherwise -> fail "structure mismatch"

-- Specific instance for TermF, only for efficiency
instance (Eq var, Eq id) => Unify (TermF id) var (Term' id var) where
  {-# SPECIALIZE instance Unify (TermF String) VName (Term String) #-}
  unify = unifyF where
   unifyF t s = do
    t' <- find t
    s' <- find s
    case (t', s') of
      (Pure vt, Pure vs) -> if vt /= vs then varBind vt s' else return ()
      (Pure vt, _)  -> if vt `Set.member` Set.fromList (vars s') then fail "occurs" else varBind vt s'
      (_, Pure vs)  -> if vs `Set.member` Set.fromList (vars t') then fail "occurs" else varBind vs t'
      (Impure t, Impure s) -> zipTermM_ unifyF t s
   zipTermM_ f (Term f1 tt1) (Term f2 tt2) | f1 == f2 = zipWithM_ f tt1 tt2
   zipTermM_ f (Tuple tt1)   (Tuple tt2) = zipWithM_ f tt1 tt2
   zipTermM_ _ (Int i1)      (Int i2)      | i1 == i2 = return ()
   zipTermM_ _ (Float f1)    (Float f2)    | f1 == f2 = return ()
   zipTermM_ _ (String s1)   (String s2)   | s1 == s2 = return ()
   zipTermM_ _ Wildcard      Wildcard                 = return ()
   zipTermM_ _ _ _ = fail "Structure mismatch"


class (Ord var, Functor termF, Monad m) => MonadEnv termF var m | m -> termF var where
    varBind :: var -> Free termF var -> m ()
    getEnv  :: m (Environment termF var)
    putEnv  :: Environment termF var -> m ()

-- ------------------------------------
-- Environments: handling substitutions
-- ------------------------------------

lookupEnv v =  (Map.lookup v . unEnv) `liftM` getEnv

find :: MonadEnv termF var m => Free termF var -> m (Free termF var)
find t0@(Pure v) = go v
  where
   go v = lookupEnv v >>= \ mb_t ->
          case mb_t of
            Just (Pure v') -> go v'
            Just t         -> varBind v t >> return t
            Nothing        -> return t0
find t0 = return t0

liftList :: MonadPlus m => [a] -> m a
liftList = msum . map return

zonk :: (Traversable termF, MonadEnv termF var m) => Free termF var -> m (Free termF var)
zonk t =  liftM join  (T.mapM f t)
  where f x = do
          x' <- lookupEnv x
          case x' of
            Nothing -> return (return x)
            Just x' -> zonk x'

newtype EnvM termF var a = EnvM {unEnvM:: (StateT (Sum Int, Environment termF var) []) a}
    deriving (Functor, Monad, MonadPlus, MonadState (Sum Int, Environment termF var))
instance Applicative (EnvM termF var) where (<*>) = ap; pure = return

execEnvM = (`execStateT` mempty) . unEnvM
execEnvM' i = (`execStateT` (Sum i, mempty)) . unEnvM
evalEnvM  env   = (`evalStateT` (mempty,env)) . unEnvM
evalEnvM' env i = (`evalStateT` (Sum  i,env)) . unEnvM

instance (Functor termF, Ord var) => MonadEnv termF var (EnvM termF var) where
  getEnv = snd `liftM` get
  putEnv = modify . second . const
  varBind v t = do {e <- getEnv; putEnv (liftEnv (Map.insert v t) e)}

instance (Monad m, Functor termF, Ord var) => MonadEnv termF var (StateT (Environment termF var) m) where
  getEnv = get
  putEnv = modify . const
  varBind v t = do {e <- getEnv; putEnv (liftEnv (Map.insert v t) e)}

instance (Monoid w, Functor termF, MonadEnv termF var m) => MonadEnv termF var (WriterT w m) where
  getEnv = lift getEnv
  putEnv = lift . putEnv
  varBind = (lift.) . varBind

deriving instance Enum (Sum Int)

class Monad m => MonadFresh var m | m -> var where freshVar :: m var
instance MonadFresh VName (EnvM termF VName) where freshVar = (Auto . getSum . fst) <$> get <* modify (first succ)
instance MonadFresh VName (State (Sum Int))  where freshVar = modify succ >> (Auto . getSum . Prelude.pred) <$> get
instance Monad m => MonadFresh VName (StateT (Sum Int) m)  where freshVar = modify succ >> liftM (Auto . getSum . Prelude.pred) get
instance (Monoid w, Monad m) => MonadFresh VName (RWST r w (Sum Int) m) where freshVar = modify succ >> liftM (Auto . getSum . Prelude.pred) get
instance Monoid w => MonadFresh VName (RWS r w (Sum Int)) where freshVar = modify succ >> liftM (Auto . getSum . Prelude.pred) get

--instance MonadState (Sum Int) m => MonadFresh VName m where freshVar = modify succ >> liftM (Auto . getSum . Prelude.pred) get
--instance MonadFresh var m => MonadFresh var (StateT s m) where freshVar = lift freshVar
instance (Monoid w, MonadFresh var m) => MonadFresh var (WriterT w m) where freshVar = lift freshVar


fresh :: forall termF var m .  (Ord var, MonadEnv termF var m, Traversable termF, MonadFresh var m) =>
         Free termF var -> m(Free termF var)
fresh = go where
  go  = liftM join . T.mapM f
  f v = do
          env <- getEnv
          v' <- lookupEnv v `const` env
          case v' of
            Just v' -> return v'
            Nothing -> do {v' <- freshVar; varBind v (return v'); return (return v')}

fmap3   = fmap.fmap.fmap
mapM3   = mapM.mapM2
mapM2   = mapM.mapM
forEach = flip map
snub    = Set.toList . Set.fromList
