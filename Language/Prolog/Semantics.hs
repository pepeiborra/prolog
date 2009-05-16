
{-# LANGUAGE NoMonomorphismRestriction, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, UndecidableInstances, OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

-- | This is a simple Prolog evaluator written just for fun.
--   It does not support anything apart from basic Logic Programming,
--   i.e. no Cut, no arithmetic, no E/S.

module Language.Prolog.Semantics (
        eval, debug,
        Unify(..), unify, unifies, equiv,
        Match(..), match, matches,
        zonk,
        Environment, MonadFresh(..), GetFresh(..))
   where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM, zipWithM, zipWithM_, msum, MonadPlus(..), join, ap, (>=>))
import Control.Monad.Free hiding (mapM)
import Control.Monad.Free.Zip
import Control.Monad.Identity (Identity)
import Control.Monad.RWS (RWS, RWST)
import Control.Monad.State  (State, StateT(..), MonadState(..), execStateT, evalState, evalStateT, modify, MonadTrans(..))
import Control.Monad.Writer (WriterT(..), MonadWriter(..), execWriterT)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Foldable (foldMap, toList, Foldable)
import Data.Maybe(isJust)
import Data.Monoid
import Data.Traversable as T
import Data.Map (Map)
import Text.PrettyPrint

import Prelude hiding (mapM)

import Debug.Trace

import Language.Prolog.Syntax

newtype Environment termF var = Env {unEnv::Map var (Free termF var)}
  deriving (Monoid)
liftEnv f (Env e) = Env (f e)

instance (Ppr var, Ppr (Free termF var)) => Ppr (Environment termF var) where
    ppr = braces . hcat . punctuate comma . map (\(v,t) -> ppr v <+> equals <+> ppr t) . Map.toList . unEnv

restrictTo :: Ord var => [var] -> Environment id var -> Environment id var
restrictTo vv = liftEnv f where
  f e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

eval  :: (Eq idp, term ~ Free termF var, Enum var, Ord var, MonadFresh var (EnvM termF var), GetVars var var, Traversable termF, Unify termF var term) => Program'' idp term -> GoalF idp term -> [Environment termF var]
eval pgm q = (fmap (restrictTo (snub $ getVars q) .  zonkEnv) . execEnvM' i . runWriterT . run pgm) q
    where zonkEnv env = liftEnv (\m -> head $ evalEnvM env (mapM zonk m)) env
          i = maximum (map fromEnum (getVars q)) + 1

debug :: (Eq idp, Ppr id, Ppr idp, Eq id, term ~ Term' id VName) => Program'' idp term -> GoalF idp term -> [ [[GoalF idp term]] ]
debug pgm q =  ((`evalStateT` (Sum i, mempty)) . unEnvM . execWriterT . run pgm) q
  where
    i = maximum [ i | Auto i <- getVars q] + 1
--run :: (Eq id, Ppr id, Ppr idp, Eq idp, term ~ Term' id var, var ~ VName, MonadPlus m, MonadFresh id var m, MonadEnv id var m, MonadWriter [[GoalF idp term]] m) => Program'' idp term -> Goal idp term -> m ()
run pgm query = go [query] where
  go []         = return ()
  go (Cut:rest) = go rest
  go prob@(goal:rest) = do
        mapM2 zonk prob >>= \prob' -> tell [prob']
        head :- body <- liftList pgm >>= getFresh
        unify goal head
        go (body ++ rest)

-- -----------
-- Unification
-- -----------
unifies :: forall termF var t . (Unify termF var t, Ord var) => t -> t -> Bool
unifies t u = isJust (evalStateT (unify t u) (mempty :: Environment termF var))

class (Traversable termF, Eq (termF ()), Eq var) => Unify termF var t | t -> termF var where unify :: MonadEnv termF var m => t -> t -> m ()

-- Generic instance
instance (Traversable f, Eq var, Eq (f ())) => Unify f var (Free f var) where
  unify t s = do
    t' <- find t
    s' <- find s
    unifyOne t' s'
   where
     unifyOne (Pure vt) s@(Pure vs) = if vt /= vs then varBind vt s else return ()
     unifyOne (Pure vt) s           = {- if vt `Set.member` Set.fromList (vars s) then fail "occurs" else-} varBind vt s
     unifyOne t           (Pure vs) = {-if vs `Set.member` Set.fromList (vars t) then fail "occurs" else-} varBind vs t
     unifyOne t         s           = zipFree_ unify t s

-- Specific instance for TermF, only for efficiency
instance (Eq var, Eq id) => Unify (TermF id) var (Term' id var) where
  {-# SPECIALIZE instance Unify (TermF String) VName (Term String) #-}
  unify = unifyF where
   unifyF t s = do
    t' <- find t
    s' <- find s
    case (t', s') of
      (Pure vt, Pure vs) -> if vt /= vs then varBind vt s' else return ()
      (Pure vt, _)  -> {-if vt `Set.member` Set.fromList (vars s') then fail "occurs" else-} varBind vt s'
      (_, Pure vs)  -> {-if vs `Set.member` Set.fromList (vars t') then fail "occurs" else-} varBind vs t'
      (Impure t, Impure s) -> zipTermM_ unifyF t s
   zipTermM_ f (Term f1 tt1) (Term f2 tt2) | f1 == f2 = zipWithM_ f tt1 tt2
   zipTermM_ f (Tuple tt1)   (Tuple tt2) = zipWithM_ f tt1 tt2
   zipTermM_ _ (Int i1)      (Int i2)      | i1 == i2 = return ()
   zipTermM_ _ (Float f1)    (Float f2)    | f1 == f2 = return ()
   zipTermM_ _ (String s1)   (String s2)   | s1 == s2 = return ()
   zipTermM_ _ Wildcard      Wildcard                 = return ()
   zipTermM_ _ _ _ = fail "Structure mismatch"


instance (Unify termF var t, Foldable f) => Unify termF var (f t) where
  unify t u = zipWithM_ unify (toList t) (toList u)

-- ---------
-- Matching
-- ---------
matches :: forall termF var t. (Match termF var t, Ord var) => t -> t -> Bool
matches t u = isJust (evalStateT (match t u) (mempty :: Environment termF var))

class (Eq (termF ()), Traversable termF) => Match termF var t | t -> termF var where match :: MonadEnv termF var m => t -> t -> m ()
instance (Traversable termF, Eq (termF ())) =>  Match termF var (Free termF var) where
  match t s = do
    t' <- find t
    s' <- find s
    matchOne t' s'
    where matchOne (Pure v) u = varBind v u
          matchOne t        u = zipFree_ match t u

instance (Match termF var t, Foldable f) => Match termF var (f t) where
  match t u = zipWithM_ match (toList t) (toList u)

-- --------------------------
-- Equivalence up to renaming
-- --------------------------

equiv ::  (Ord var, Enum var, Ord (termF (Free termF var)),
           MonadFresh var (EnvM termF var), Unify termF var t, GetVars var t, GetFresh termF var t) => t -> t -> Bool
equiv t u = case execEnvM' i (unify t =<< getFresh u) of
              [x] -> isRenaming x
              _   -> False
 where
     i = maximum (map fromEnum (getVars t)) + 1
--    isRenaming :: (Functor termF, Ord var, Ord (termF (Free termF var))) => Environment termF var -> Bool
     isRenaming (unEnv -> subst) = all isVar (Map.elems subst) && isBijective (Map.mapKeysMonotonic return  subst)

--    isBijective :: Ord k => Map.Map k k -> Bool
     isBijective rel = -- cheap hackish bijectivity check.
                    -- Ensure that the relation is injective and its inverse is too.
                    -- The sets of variables must be disjoint too
                    -- Actually there should be no need to check the inverse
                    -- since this is a Haskell Map and hence the domain contains no duplicates
                   Set.size elemsSet == Map.size rel &&
                   (Map.keysSet rel) `Set.intersection` elemsSet == Set.empty
       where
          elemsSet = Set.fromList(Map.elems rel)


-- ------------------------------------
-- Environments: handling substitutions
-- ------------------------------------

class (Ord var, Functor termF, Monad m) => MonadEnv termF var m | m -> termF var where
    varBind :: var -> Free termF var -> m ()
    getEnv  :: m (Environment termF var)
    putEnv  :: Environment termF var -> m ()

lookupEnv v =  (Map.lookup v . unEnv) `liftM` getEnv

find :: MonadEnv termF var m => Free termF var -> m (Free termF var)
find t0@(Pure v) = go v
  where
   go x = lookupEnv x >>= \ mb_t ->
          case mb_t of
            Just (Pure x') -> go x'
            Just t         -> varBind v t >> return t
            Nothing        -> return (Pure x)
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

execEnvM    = fmap snd . (`execStateT` mempty) . unEnvM
execEnvM' i = fmap snd . (`execStateT` (Sum i, mempty)) . unEnvM
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
instance Monad m => MonadFresh v (StateT [v] m)  where freshVar = do { x:xx <- get; put xx; return x}
instance  MonadFresh v (State [v])  where freshVar = do { x:xx <- get; put xx; return x}
instance (Monoid w, Monad m) => MonadFresh v (RWST r w [v] m) where freshVar = do { x:xx <- get; put xx; return x}
instance (Monoid w, MonadFresh var m) => MonadFresh var (WriterT w m) where freshVar = lift freshVar

fresh ::  (MonadTrans t, MonadEnv termF var (t m), Traversable termF, MonadFresh var m) =>
         Free termF var -> t  m(Free termF var)
fresh = go where
  go  = liftM join . T.mapM f
  f v = do
          env <- getEnv
          v' <- lookupEnv v `const` env
          case v' of
            Just v' -> return v'
            Nothing -> do {v' <- lift freshVar; varBind v (return v'); return (return v')}

class (Ord var, Traversable termF) => GetFresh (termF :: * -> *) var t | t -> termF var where
    getFreshF :: (MonadEnv termF var (tm m), MonadFresh var m, MonadTrans tm) => t -> tm m t
instance (Ord var, Traversable termF) => GetFresh termF var (Free termF var) where
    getFreshF t = fresh t
instance (Ord var, Traversable termF, GetFresh termF var t, Traversable f) => GetFresh termF var (f t) where
    getFreshF t = mapM getFreshF t

getFresh :: forall t termF var m . (GetFresh termF var t, MonadFresh var m) => t -> m t
getFresh t = evalStateT (getFreshF t) (mempty :: Environment termF var)

fmap3   = fmap.fmap.fmap
mapM3   = mapM.mapM2
mapM2   = mapM.mapM
forEach = flip map
snub    = Set.toList . Set.fromList
