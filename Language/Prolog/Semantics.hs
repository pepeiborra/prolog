{-# LANGUAGE NoMonomorphismRestriction, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

-- | This is a simple Prolog evaluator written just for fun.
--   It does not support anything apart from basic Logic Programming,
--   i.e. no Cut, no arithmetic, no E/S.

module Language.Prolog.Semantics where -- (eval, debug, unify, zonk, Environment) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM, zipWithM, zipWithM_, msum, MonadPlus(..), join, ap, (>=>))
import Control.Monad.Free hiding (mapM)
import Control.Monad.Free.Zip
import Control.Monad.State  (StateT(..), MonadState(..), execStateT, evalStateT, modify, MonadTrans(..))
import Control.Monad.Writer (WriterT(..), MonadWriter(..), execWriterT)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Foldable (foldMap, toList)
import Data.Monoid
import Data.Traversable as T
import Data.Map (Map)
import Text.PrettyPrint

import Prelude hiding (mapM)

import Language.Prolog.Syntax

type Goal id var = [Atom id]
type Environment id var = Map var (Term' id var)
deriving instance Ord VName

instance (Ppr var, Show id) => Ppr (Environment id var) where
    ppr = fcat . punctuate comma . map (\(v,t) -> ppr v <+> equals <+> ppr t) . Map.toList

restrictTo :: Ord var => [var] -> Environment id var -> Environment id var
restrictTo vv e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

eval  :: Eq id => Program id -> Atom id -> [Environment id VName]
eval pgm q = (fmap (restrictTo (snub $ foldMap vars q) .  zonkEnv . snd) . execEnvM . run pgm) q
    where zonkEnv env = head $ evalEnvM env (mapM zonk env)

debug :: (Eq id) => Program id -> Atom id -> [ [Goal id VName] ]
debug pgm = (`evalStateT` mempty) . execWriterT . unEnvM . run pgm

run :: (Eq id) => Program id -> Atom id -> EnvM id VName ()
run pgm p = go [p] pgm where
  go [] cc         = return ()
  go (Cut:rest) cc = go rest cc
  go prob@(p:rest) cc = do
        mapM2 zonk prob >>= \prob' -> tell [prob']
        h :- t <- liftList cc >>= mapM2 fresh -- TODO: modify for cut
        unify h p
        go (t  ++ rest) cc

class Eq id => Unify id var t | t -> id var where unify :: MonadEnv id var m => t -> t -> m ()
instance Eq id => Unify id var (Atom' id var) where
  unify (Pred ft t) (Pred fs s) | ft /= fs = fail "Can't unify"
  unify (Pred ft t) (Pred fs s) = zipWithM_ unify t s

instance Eq id => Unify id var (Term' id var) where
  unify = zipFree_ unifyF where
   unifyF t s = do
    t' <- lookupEnv t
    s' <- lookupEnv s
    case (t', s') of
      (Pure vt, Pure vs) -> if vt /= vs then varBind vt s' else return ()
      (Pure vt, s)       -> varBind vt s'
      (t, Pure vs)       -> varBind vs t'
      _                  -> unify t' s'

class (Ord var, MonadPlus m) => MonadEnv id var m | m -> id var where
    varBind :: var -> Term' id var -> m ()
    getEnv  :: m (Environment id var)
    putEnv  :: Environment id var -> m ()

lookupEnv  v =  getEnv >>= maybe (return $ return v) return . Map.lookup v
lookupEnv' v =  Map.lookup v `liftM` getEnv

liftList :: Ord var => [a] -> EnvM id var a
liftList = EnvM . lift . lift

zonk :: (MonadEnv id var m) => Term' id var -> m (Term' id var)
zonk =  liftM join . T.mapM f
  where f x = do
          x' <- lookupEnv' x
          case x' of
            Nothing -> return (return x)
            Just x' -> zonk x'

newtype EnvM id var a = EnvM {unEnvM::WriterT [Goal id var] (StateT (Sum Int, Environment id var) []) a}
    deriving (Functor, Monad, MonadPlus, MonadState (Sum Int, Environment id var), MonadWriter [Goal id var])
instance Applicative (EnvM id var) where (<*>) = ap; pure = return

execEnvM = (`execStateT` mempty) . runWriterT . unEnvM
evalEnvM  env   = fmap fst . (`evalStateT` (mempty,env)) . runWriterT . unEnvM
evalEnvM' env i = fmap fst . (`evalStateT` (Sum  i,env)) . runWriterT . unEnvM

instance Ord var => MonadEnv id var (EnvM id var) where
  getEnv = snd `liftM` get
  putEnv = modify . second . const
  varBind v t = do {e <- getEnv; putEnv (Map.insert v t e)}

instance (MonadPlus m, Ord var) => MonadEnv id var (StateT (Environment id var) m) where
  getEnv = get
  putEnv = modify . const
  varBind v t = do {e <- getEnv; putEnv (Map.insert v t e)}

deriving instance Enum (Sum Int)
class Monad m => MonadFresh id var m where freshVar :: m (Term' id var)
instance MonadFresh id VName (EnvM id VName) where freshVar = (var'.getSum.fst) <$> get <* modify (first succ)
instance MonadFresh id var m => MonadFresh id var (StateT s m) where freshVar = lift freshVar

fresh :: forall id var m . (MonadFresh id var m, MonadEnv id var m) => Term' id var -> m (Term' id var)
fresh = flip evalStateT (mempty :: Environment id var) . go where
  go  = liftM join . T.mapM f
  f v = do
          v' <- lift $ lookupEnv' v
          case v' of
            Just v' -> go v'
            Nothing -> do {v' <- lift freshVar; varBind v v'; return v'}

fmap3   = fmap.fmap.fmap
mapM3   = mapM.mapM2
mapM2   = mapM.mapM
forEach = flip map
snub    = Set.toList . Set.fromList
