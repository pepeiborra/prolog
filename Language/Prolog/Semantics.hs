{-# LANGUAGE NoMonomorphismRestriction, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Language.Prolog.Semantics (eval, debug, unify, zonk, Environment) where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad (liftM, zipWithM, zipWithM_, msum, MonadPlus(..), ap)
import Control.Monad.State  (StateT(..), MonadState(..), execStateT, evalStateT, modify, MonadTrans(..))
import Control.Monad.Writer (WriterT(..), MonadWriter(..), execWriterT)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Foldable (foldMap, toList)
import Data.Monoid
import Data.Traversable
import Data.Map (Map)
import Text.PrettyPrint

import Prelude hiding (mapM)

import Language.Prolog.Syntax

type Goal id = [Atom id]
type Environment id = Map VName (Term id)
deriving instance Ord VName

instance Show id => Ppr (Environment id) where
    ppr = fcat . punctuate comma . map (\(v,t) -> ppr v <+> equals <+> ppr t) . Map.toList

restrictTo :: [VName] -> Environment id -> Environment id
restrictTo vv e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

eval  :: Eq id => Program id -> Atom id -> [Environment id]
eval pgm q = (fmap (restrictTo (snub $ foldMap vars q) .  zonkEnv . snd) . execEnvM . run pgm) q
    where zonkEnv env = head $ evalEnvM env (mapM zonk env)

debug :: Eq id => Program id -> Atom id -> [ [Goal id] ]
debug pgm = (`evalStateT` mempty) . execWriterT . unEnvM . run pgm

--run :: (MonadWriter [Goal] m, MonadTrans m, MonadEnv m, MonadFresh m) => Program -> Atom -> m ()
run :: Eq id => Program id -> Atom id -> EnvM id ()
run pgm p = go [p] pgm where
  go [] cc         = return ()
  go (Cut:rest) cc = go rest cc
  go prob@(p:rest) cc = do
        mapM2 zonk prob >>= \prob' -> tell [prob']
        h :- t <- liftList cc >>= fresh -- TODO: modify for cut
        unify h p
        go (t  ++ rest) cc

class Eq id => Unify id t | t -> id where unify :: MonadEnv id m => t -> t -> m ()
instance Eq id => Unify id (Atom id) where
  unify (Pred ft t) (Pred fs s) | ft /= fs = fail "Can't unify"
  unify (Pred ft t) (Pred fs s) = zipWithM_ unify t s

instance Eq id => Unify id (Term id) where
  unify t s = do
    t' <- find t
    s' <- find s
    case (out t', out s') of
      (Term ft st, Term fs ss) | ft == fs -> zipWithM_ unify st ss
      (Var vt, Var vs) -> if vt /= vs then varBind vt s' else return ()
      (Var vt, s)      -> varBind vt s'
      (t, Var vs)      -> varBind vs t'
      _                -> fail "Can't unify"

class MonadPlus m => MonadEnv id m | m -> id where
    varBind :: VName -> Term id -> m ()
    find    :: Term id  -> m (Term id)
    getEnv  :: m (Environment id)
    putEnv  :: Environment id -> m ()

zonk :: MonadEnv id m => Term id -> m (Term id)
zonk x = do
  x' <- find x
  case x' of
    (out -> Term f tt) -> do
            tt' <- mapM zonk tt
            return (term f tt')
    _ -> return x'

newtype EnvM id a = EnvM {unEnvM::WriterT [Goal id] (StateT (Int, Environment id) []) a}
    deriving (Functor, Monad, MonadPlus, MonadState (Int, Environment id), MonadWriter [Goal id])
type SavePoint id = Environment id

instance Applicative (EnvM id) where (<*>) = ap; pure = return
instance Monoid Int where mempty = 0; mappend = (+)

execEnvM = (`execStateT` mempty) . runWriterT . unEnvM
evalEnvM env = fmap fst . (`evalStateT` (mempty,env)) . runWriterT . unEnvM

liftList :: [a] -> EnvM id a
liftList = EnvM . lift . lift

instance MonadEnv id (EnvM id) where
  getEnv = snd `liftM` get
  putEnv = modify . second . const

  find t@(out -> Var v) = do
    mb_val <- lookupEnv v
    case mb_val of
      Nothing -> return t
      Just val -> do {t' <- find val; varBind v t'; return t'}
    where lookupEnv v = Map.lookup v <$> getEnv
  find x = return x

  varBind v t = do {e <- getEnv; putEnv (Map.insert v t e)}

class Monad m => MonadFresh m where freshVar :: m (Term id)
instance MonadFresh (EnvM id) where freshVar = (var'.fst) <$> get <* modify (first succ)
instance MonadFresh m => MonadFresh (StateT s m) where freshVar = lift freshVar

class    Fresh id a | a -> id where freshF :: (MonadFresh m, MonadState (Map VName (Term id)) m) => a -> m a
instance Fresh id (Term id)   where
  freshF (out -> Var v) = get >>= \st -> case Map.lookup v st of
                                           Just v' -> return v'
                                           Nothing -> do {v' <- freshVar; put (Map.insert v v' st); return v'}
  freshF (out -> Term f tt) = term f `liftM` mapM freshF tt

instance Fresh id (Atom id)   where freshF (Pred f tt) = Pred f `liftM` (mapM freshF tt)
instance Fresh id (Clause id) where freshF (h :- c) = (:-) `liftM` freshF h `ap` mapM freshF c

fresh =  (`evalStateT` mempty) . freshF

--subTerms :: Term -> [Term]
--subTerms = foldMap toList

fmap3   = fmap.fmap.fmap
mapM3   = mapM.mapM2
mapM2   = mapM.mapM
forEach = flip map
snub    = Set.toList . Set.fromList
