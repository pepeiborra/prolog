{-# LANGUAGE NoMonomorphismRestriction, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

-- | This is a simple Prolog evaluator written just for fun.
--   It does not support anything apart from basic Logic Programming,
--   i.e. no Cut, no arithmetic, no E/S.

module Language.Prolog.Semantics (eval, debug, unify, zonk, Environment) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM, zipWithM, zipWithM_, msum, MonadPlus(..), join, ap, (>=>))
import Control.Monad.Free hiding (mapM)
import Control.Monad.Free.Zip
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

type Goal id term = AtomF id term
newtype Environment id var = Env {unEnv::Map var (Term' id var)}
  deriving (Eq, Show, Monoid)
liftEnv f (Env e) = Env (f e)

deriving instance Ord VName

instance (Ppr var, Ppr id) => Ppr (Environment id var) where
    ppr = braces . hcat . punctuate comma . map (\(v,t) -> ppr v <+> equals <+> ppr t) . Map.toList . unEnv

restrictTo :: Ord var => [var] -> Environment id var -> Environment id var
restrictTo vv = liftEnv f where
  f e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

eval  :: (Ppr id, Ppr idp, Eq id, Eq idp, term ~ Term' id VName) => Program'' idp term -> Goal idp term -> [Environment id VName]
eval pgm q = (fmap (restrictTo (snub $ foldMap vars q) .  zonkEnv . snd) . execEnvM' i . runWriterT . run pgm) q
    where zonkEnv env = liftEnv (\m -> head $ evalEnvM env (mapM zonk m)) env
          i = maximum [ i | Auto i <- foldMap vars q] + 1

debug :: (Eq idp, Ppr id, Ppr idp, Eq id, term ~ Term' id VName) => Program'' idp term -> Goal idp term -> [ [[Goal idp term]] ]
debug pgm q =  ((`evalStateT` (Sum i, mempty)) . unEnvM . execWriterT . run pgm) q
  where
    i = maximum [ i | Auto i <- foldMap vars q] + 1
run :: (Eq id, Ppr id, Ppr idp, Eq idp, term ~ Term' id var, var ~ VName, MonadPlus m, MonadFresh id var m, MonadEnv id var m, MonadWriter [[Goal idp term]] m) => Program'' idp term -> Goal idp term -> m ()
run pgm p = go [p] where
  go []         = return ()
  go (Cut:rest) = go rest
  go prob@(p:rest) = do
        env <- getEnv
        mapM2 zonk prob >>= \prob' -> tell [prob']
        h :- t <- liftList pgm >>= \r -> (flip evalStateT (mempty `asTypeOf` env) . mapM2 fresh) r -- TODO: modify for cut
        unify p h `const` env `const` (h :- t) `const` rest
--        zprob <- mapM2 zonk (t ++ rest)
--        trace (show $ ppr env <+> ppr zprob) (return ())
        go (t ++ rest)

class Eq id => Unify id var t | t -> id var where unify :: MonadEnv id var m => t -> t -> m ()
instance (Eq id, Eq idp) => Unify id var (AtomF idp (Term' id var)) where
  unify (Pred ft t) (Pred fs s) | ft /= fs = fail "Can't unify"
  unify (Pred ft t) (Pred fs s) = zipWithM_ unify t s

instance Eq id => Unify id var (Term' id var) where
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

class (Ord var, Monad m) => MonadEnv id var m | m -> id var where
    varBind :: var -> Term' id var -> m ()
    getEnv  :: m (Environment id var)
    putEnv  :: Environment id var -> m ()

lookupEnv v =  (Map.lookup v . unEnv) `liftM` getEnv

find :: MonadEnv id var m => Term' id var -> m (Term' id var)
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

zonk :: (MonadEnv id var m) => Term' id var -> m (Term' id var)
zonk t =  liftM join  (T.mapM f t)
  where f x = do
          x' <- lookupEnv x
          case x' of
            Nothing -> return (return x)
            Just x' -> zonk x'

newtype EnvM id var a = EnvM {unEnvM:: (StateT (Sum Int, Environment id var) []) a}
    deriving (Functor, Monad, MonadPlus, MonadState (Sum Int, Environment id var))
instance Applicative (EnvM id var) where (<*>) = ap; pure = return

execEnvM = (`execStateT` mempty) . unEnvM
execEnvM' i = (`execStateT` (Sum i, mempty)) . unEnvM
evalEnvM  env   = (`evalStateT` (mempty,env)) . unEnvM
evalEnvM' env i = (`evalStateT` (Sum  i,env)) . unEnvM

instance Ord var => MonadEnv id var (EnvM id var) where
  getEnv = snd `liftM` get
  putEnv = modify . second . const
  varBind v t = do {e <- getEnv; putEnv (liftEnv (Map.insert v t) e)}

instance (Monad m, Ord var) => MonadEnv id var (StateT (Environment id var) m) where
  getEnv = get
  putEnv = modify . const
  varBind v t = do {e <- getEnv; putEnv (liftEnv (Map.insert v t) e)}

instance (Monoid w, MonadEnv id var m) => MonadEnv id var (WriterT w m) where
  getEnv = lift getEnv
  putEnv = lift . putEnv
  varBind = (lift.) . varBind

deriving instance Enum (Sum Int)
class Monad m => MonadFresh id var m where freshVar :: m (Term' id var)
instance MonadFresh id VName (EnvM id VName)   where freshVar = (var'.getSum.fst) <$> get <* modify (first succ)
--instance MonadFresh id VName (State (Sum Int)) where freshVar = (var'.getSum) <$> get <* modify succ
instance MonadFresh id var m => MonadFresh id var (StateT s m) where freshVar = lift freshVar
instance (Monoid w, MonadFresh id var m) => MonadFresh id var (WriterT w m) where freshVar = lift freshVar


fresh :: forall id var m .  (Ord var, MonadEnv id var m, MonadFresh id var m) => Term' id var -> m(Term' id var)
fresh = go where
  go  = liftM join . T.mapM f
  f v = do
          env <- getEnv
          v' <- lookupEnv v `const` env
          case v' of
            Just v' -> return v'
            Nothing -> do {v' <- freshVar; varBind v v'; return v'}

fmap3   = fmap.fmap.fmap
mapM3   = mapM.mapM2
mapM2   = mapM.mapM
forEach = flip map
snub    = Set.toList . Set.fromList

{-
--zonk' :: (MonadEnv id var m) => Term' id var -> m (Term' id var)
zonk' (Impure (Term id tt)) = join $ liftM (Impure . Term id) (T.mapM f tt) -- :: m (Term' id (Term' id var))
  where f x = do
          x' <- lookupEnv' x
          case x' of
            Nothing -> return (return x)
            Just x' -> zonk x'
-}