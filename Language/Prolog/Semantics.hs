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

import Control.Monad.Free hiding (mapM)
import Control.Monad.Logic (LogicT, MonadLogic(..), observeAll)
import Control.Monad.Variant (runVariantT')
import Control.Monad.Writer (WriterT(..), MonadWriter(..), execWriterT)
import qualified Data.Set as Set
import Data.Traversable as T
import Data.Term.Rules
import Data.Term.Var
import Data.Term hiding (unify, Var)
import qualified Data.Term as Family
import Text.PrettyPrint.HughesPJClass
import Debug.Hoed.Observe

import Prelude hiding (mapM)

import Language.Prolog.Syntax

eval  :: ( Eq idp, term ~ Free termF var, Enum var, Ord var, Rename var, Observable var
         , Traversable termF, Unify termF) => Program'' idp term -> GoalF idp term -> [Substitution termF var]
eval pgm q = (fmap (restrictTo vq .  zonkSubst . snd) . filter (fst.fst) . observeAll . runVariantT' vq . runMEnv . runWriterT . run pgm) q
    where vq = Set.toList(getVars q)

debug :: (Eq id, Eq idp, term ~ Term' id Var) => Program'' idp term -> GoalF idp term -> [[Trace idp term]]
debug pgm q =  (observeAll . runVariantT' vq . evalMEnv . execWriterT . run pgm) q
   where
     vq = Set.toList $ getVars q

run :: forall var var0 termF idp term term0 m.
       (Ord var, Ord var0, Rename var0, Observable var0, Observable var,
        Eq idp,
        Unify termF,
        term0 ~ Free termF var0,
        term  ~ Free termF var,
        var ~ Family.Var m,
        termF ~ Family.TermF m,
        MonadLogic m, MonadEnv m, MonadVariant m, MonadWriter [Trace idp term] m) =>
       Program'' idp term0 -> GoalF idp term -> m Bool
run pgm query = go [query] where
  go []         = return True
  go (Cut:rest) = go rest
  go prob@(goal:rest) = do
        head :- body <- liftList pgm >>= \c -> (mapM.mapM) (freshWith' (flip const)) c
        zg <- mapM (zonkM return) goal
        tell [Call zg head]
        ifte (getUnifierM goal head)
             (\_ -> do
                 mapM (zonkM return) zg >>= \zg' -> tell [Exit zg']
                 go (body ++ rest))
             (tell [Fail zg] >> return False)

data Trace idp term = Call (GoalF idp term)(GoalF idp term)
                    | Exit (GoalF idp term)
                    | Fail (GoalF idp term)
         deriving Show

instance (Pretty (GoalF idp term)) => Pretty (Trace idp term) where
  pPrint(Call g h) = text "Call" <+> pPrint g <+> pPrint h
  pPrint(Exit g) = text "Exit" <+> pPrint g
  pPrint(Fail g) = text "Fail" <+> pPrint g

-- -------------------
-- Liftings for LogicT
-- -------------------
type instance Family.Var (LogicT m) = Family.Var m
type instance Family.TermF (LogicT m) = Family.TermF m


-- -----------
-- Combinators
-- -----------

liftList :: MonadPlus m => [a] -> m a
liftList = msum . map return
