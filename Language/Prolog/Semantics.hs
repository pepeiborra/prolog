
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
        eval, debug, run,
        GetFresh(..), GetUnifier(..))
   where

import Control.Applicative
import Control.Arrow (first, second)
import Control.Exception as CE
import Control.Monad (liftM, zipWithM, zipWithM_, msum, MonadPlus(..), join, ap, (>=>))
import Control.Monad.Free hiding (mapM)
import Control.Monad.Free.Zip
import Control.Monad.Identity (Identity)
import Control.Monad.List (ListT(..))
import Control.Monad.Logic (Logic, LogicT, MonadLogic(..), observeAll, observeAllT)
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
import Data.Term.Var
import Data.Term.IOVar
import Data.Term hiding (unify)
import qualified Data.Term as Term
import Text.PrettyPrint

import Prelude hiding (mapM)

import Debug.Trace

import Language.Prolog.Syntax

eval  :: (Eq idp, term ~ Free termF var, Enum var, Ord var, MonadFresh var (EnvM termF var), Traversable termF, Unify termF) => Program'' idp term -> GoalF idp term -> [Substitution termF var]
eval pgm q = (fmap (restrictTo vq .  zonkSubst . snd) . filter (fst.fst) . runEnvM' i . runWriterT . run pgm) q
    where i    = maximum (0 : map fromEnum vq) + 1
          vq = snub(getVars q)
debug :: (Eq id, Eq idp, term ~ Term' id Var) => Program'' idp term -> GoalF idp term -> [[Trace idp term]]
debug pgm q =  (evalEnvM' i . execWriterT . run pgm) q
  where
    i = maximum (0 : map fromEnum (getVars q)) + 1

run :: forall var var0 termF idp term term0 m.
       (Ord var, Ord var0, Eq (termF ()), Eq idp, Traversable termF,
        term0 ~ Free termF var0, term ~ Free termF var,
        MonadLogic m, MonadEnv termF var m, MonadFresh var m, MonadWriter [Trace idp term] m) =>
       Program'' idp term0 -> GoalF idp term -> m Bool
run pgm query = go [query] where
  go []         = return True
  go (Cut:rest) = go rest
  go prob@(goal:rest) = do
        head :- body <- liftList pgm >>= \c -> evalStateT (mapM2 fresh' c) (mempty :: Substitution termF (Either var0 var))
        zg <- mapM (zonkM return) goal
        tell [Call zg head]
        ifte (getUnifier goal head)
             (\_ -> do
                 mapM (zonkM return) zg >>= \zg' -> tell [Exit zg']
                 go (body ++ rest))
             (tell [Fail zg] >> return False)

instance (Ppr var, Ppr (Free termF var)) => Ppr (Substitution termF var) where
    ppr = braces . hcat . punctuate comma . map (\(v,t) -> ppr v <+> equals <+> ppr t) . Map.toList . unSubst

data Trace idp term = Call (GoalF idp term)(GoalF idp term)
                    | Exit (GoalF idp term)
                    | Fail (GoalF idp term)
         deriving Show

instance (Ppr term, Ppr idp) => Ppr (Trace idp term) where
  ppr(Call g h) = text "Call" <+> ppr g <+> ppr h
  ppr(Exit g) = text "Exit" <+> ppr g
  ppr(Fail g) = text "Fail" <+> ppr g

-- -----------
-- Unification
-- -----------
class (Traversable termF, Eq (termF ()), Eq var) => GetUnifier termF var t | t -> termF var
    where getUnifier :: MonadEnv termF var m => t -> t -> m ()

instance (Traversable f, Eq var, Eq (f ())) => GetUnifier f var (Free f var) where
  getUnifier t u = Term.unify t u
instance (GetUnifier termF var t, Eq (f ()), Functor f, Foldable f) => GetUnifier termF var (f t) where
  getUnifier t u | fmap (const ()) t == fmap (const ()) u = zipWithM_ getUnifier (toList t) (toList u)
            | otherwise = fail "structure mismatch"
-- -----------------
-- Environment Monad
-- -----------------

newtype EnvM termF var a = EnvM {unEnvM:: (StateT (Sum Int, Substitution termF var) Logic ) a}
    deriving (Functor, Monad, MonadPlus, MonadState (Sum Int, Substitution termF var), MonadLogic)
instance Applicative (EnvM termF var) where (<*>) = ap; pure = return
deriving instance Enum (Sum Int)

instance MonadFresh Var (EnvM termF Var) where freshVar = (VAuto . getSum . fst) <$> get <* modify (first succ)
instance (Traversable termF, Ord var) => MonadEnv termF var (EnvM termF var) where
  varBind v t = do {(l,s) <- get; put (l, liftSubst (Map.insert v t) s)}
  lookupVar v = get >>= \(_,s) -> return (lookupSubst v s)

instance MonadEnv t v m => MonadEnv t v (ListT m) where
  varBind   = (lift.) . varBind
  lookupVar = lift    . lookupVar

instance (Monoid w, Functor termF, MonadEnv termF var m) => MonadEnv termF var (WriterT w m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar
instance (Functor termF, MonadEnv termF var m) => MonadEnv termF var (LogicT m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

{-
instance (Functor termF, MonadEnv termF var m) => MonadEnv termF var (StateT s m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar
-}
execEnvM    = fmap snd . observeAll . (`execStateT` mempty) . unEnvM
execEnvM' i = fmap snd . observeAll . (`execStateT` (Sum i, mempty)) . unEnvM
evalEnvM  env   = observeAll . (`evalStateT` (mempty,env)) . unEnvM
evalEnvM' i = observeAll . (`evalStateT` (Sum  i,mempty)) . unEnvM
runEnvM'  i = fmap (second snd) . observeAll . (`runStateT` (Sum  i,mempty)) . unEnvM

-- ------------------------------------------
-- GetFresh: Variants of terms and clauses
-- ------------------------------------------

class (Traversable termF) => GetFresh (termF :: * -> *) var thing | thing -> termF var where
    getFresh' :: (MonadTrans t, MonadFresh var m, MonadEnv termF var (t m)) => thing -> t m thing
instance (Traversable termF) => GetFresh termF var (Free termF var) where
    getFresh' t = fresh t
instance (Traversable termF, GetFresh termF var t, Traversable f) => GetFresh termF var (f t) where
    getFresh' t = mapM getFresh' t

getFresh :: forall t v m thing. (Ord v, MonadFresh v m, GetFresh t v thing) => thing -> m thing
getFresh t = evalStateT (getFresh' t) (mempty :: Substitution t v)

instance (Monoid w, MonadFresh var m) => MonadFresh var (WriterT w m) where freshVar = lift freshVar
instance MonadFresh var m => MonadFresh var (ListT    m) where freshVar = lift freshVar
instance MonadFresh var m => MonadFresh var (StateT s m) where freshVar = lift freshVar
instance MonadFresh var m => MonadFresh var (LogicT   m) where freshVar = lift freshVar

-- -----------
-- Combinators
-- -----------
mapM3 = mapM.mapM.mapM
mapM2 = mapM.mapM
snub  = Set.toList . Set.fromList

liftList :: MonadPlus m => [a] -> m a
liftList = msum . map return
