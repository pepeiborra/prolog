{-# LANGUAGE NoMonomorphismRestriction, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances #-}
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

type Goal = [Pred]
type Environment = Map VName Term
deriving instance Ord VName

instance Ppr Environment where
    ppr = fcat . punctuate comma . map (\(v,t) -> ppr v <+> equals <+> ppr t) . Map.toList

restrictTo :: [VName] -> Environment -> Environment
restrictTo vv e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

eval  :: Program -> Pred -> [Environment]
eval pgm q = (fmap (restrictTo (snub $ foldMap vars q) .  zonkEnv . snd) . execEnvM . run pgm) q
    where zonkEnv env = head $ evalEnvM env (mapM zonk env)

debug :: Program -> Pred -> [ [Goal] ]
debug pgm = (`evalStateT` mempty) . execWriterT . unEnvM . run pgm

--run :: (MonadWriter [Goal] m, MonadTrans m, MonadEnv m, MonadFresh m) => Program -> Pred -> m ()
run :: Program -> Pred -> EnvM ()
run pgm p = go [p] where
  go [] = return ()
  go prob@(p:rest) = do
        mapM2 zonk prob >>= \prob' -> tell [prob']
        h :- t <- liftList pgm >>= fresh
        unify h p
        go (t  ++ rest)

class Unify t where unify :: MonadEnv m => t -> t -> m ()
instance Unify Pred where
  unify (Pred ft t) (Pred fs s) | ft /= fs = fail "Can't unify"
  unify (Pred ft t) (Pred fs s) = zipWithM_ unify t s

instance Unify Term where
  unify t s = do
    t' <- find t
    s' <- find s
    case (out t', out s') of
      (Term ft st, Term fs ss) | ft == fs -> zipWithM_ unify st ss
      (Var vt, Var vs) -> if vt /= vs then varBind vt s' else return ()
      (Var vt, s)      -> varBind vt s'
      (t, Var vs)      -> varBind vs t'
      _                -> fail "Can't unify"

class MonadPlus m => MonadEnv m where
    varBind :: VName -> Term -> m ()
    find    :: Term  -> m Term
    getEnv  :: m Environment
    putEnv  :: Environment -> m ()

zonk :: MonadEnv m => Term -> m Term
zonk x = do
  x' <- find x
  case x' of
    (out -> Term f tt) -> do
            tt' <- mapM zonk tt
            return (term f tt')
    _ -> return x'

newtype EnvM a = EnvM {unEnvM::WriterT [Goal] (StateT (Int, Environment) []) a}
    deriving (Functor, Monad, MonadPlus, MonadState (Int, Environment), MonadWriter [Goal])
type SavePoint = Environment

instance Applicative EnvM where (<*>) = ap; pure = return
instance Monoid Int where mempty = 0; mappend = (+)

execEnvM = (`execStateT` mempty) . runWriterT . unEnvM
evalEnvM env = fmap fst . (`evalStateT` (mempty,env)) . runWriterT . unEnvM

liftList :: [a] -> EnvM a
liftList = EnvM . lift . lift

instance MonadEnv EnvM where
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

class Monad m => MonadFresh m where freshVar :: m Term
instance MonadFresh EnvM where freshVar = (var'.fst) <$> get <* modify (first succ)
instance MonadFresh m => MonadFresh (StateT s m) where freshVar = lift freshVar

class    Fresh a      where freshF :: (MonadFresh m, MonadState (Map VName Term) m) => a -> m a
instance Fresh Term   where
  freshF (out -> Var v) = get >>= \st -> case Map.lookup v st of
                                           Just v' -> return v'
                                           Nothing -> do {v' <- freshVar; put (Map.insert v v' st); return v'}
  freshF (out -> Term f tt) = term f `liftM` mapM freshF tt

instance Fresh Pred   where freshF (Pred f tt) = Pred f `liftM` (mapM freshF tt)
instance Fresh Clause where freshF (h :- c) = (:-) `liftM` freshF h `ap` mapM freshF c

fresh =  (`evalStateT` mempty) . freshF

--subTerms :: Term -> [Term]
--subTerms = foldMap toList

fmap3   = fmap.fmap.fmap
mapM3   = mapM.mapM2
mapM2   = mapM.mapM
forEach = flip map
snub    = Set.toList . Set.fromList
