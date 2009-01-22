{-# LANGUAGE StandaloneDeriving, FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances #-}
module Language.Prolog.Syntax where

import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Traversable

import Text.PrettyPrint

type Program = [Clause]
data ClauseF f = f :- [f] deriving (Eq, Show)
instance Functor     ClauseF where fmap     f (h :- c) = f h :- fmap f c
instance Foldable    ClauseF where foldMap  f (h :- c) = f h `mappend` foldMap f c
instance Traversable ClauseF where traverse f (h :- c) = (:-) <$> f h <*> traverse f c

data PredF f   = Pred Atom [f]  deriving (Eq, Show)
instance Functor     PredF where fmap     f (Pred a tt) = Pred a (fmap f tt)
instance Foldable    PredF where foldMap  f (Pred a tt) = foldMap f tt
instance Traversable PredF where traverse f (Pred a tt) = Pred a <$> traverse f tt

data TermF f = Term Atom [f] | Var VName deriving (Eq, Show)
instance Functor TermF where fmap f (Term a tt) = Term a (fmap f tt)

data In f = In {out::f (In f)}
deriving instance Eq (f(In f)) => Eq (In f)
deriving instance Show (f(In f)) => Show (In f)

type Clause = ClauseF Pred
type Pred   = PredF Term
type Term   = In TermF
data VName  = VName String | Auto Int deriving (Eq, Show)
type Atom   = String

term :: Atom -> [Term] -> Term
term f = In . Term f

var :: Atom -> Term
var  = In . Var . VName

var' :: Int -> Term
var' = In . Var . Auto

class Ppr a where ppr :: a -> Doc
instance Ppr a => Ppr (TermF a) where
    ppr (Var v)  = ppr v
    ppr (Term f []) = text f
    ppr (Term f tt) = text f <> parens (fcat (punctuate comma $ map ppr tt))

instance Ppr VName where
    ppr (VName v)  = text v
    ppr (Auto v_i) = text "V" <> int v_i

instance Ppr Pred where
    ppr (Pred f []) = text f
    ppr (Pred f tt) = text f <> parens(fcat (punctuate comma $ map ppr tt))

instance Ppr (f(In f)) => Ppr (In f) where ppr (In t) = ppr t
instance Ppr Clause  where
    ppr (h :- []) = ppr h <> char '.'
    ppr (h :- t) = ppr h <+> text ":-" <+> fcat(punctuate comma (map ppr t)) <> char '.'
instance Ppr Program where ppr = vcat . map ppr
{-
instance Show Program where show = render . ppr
instance Show Clause  where show = render . ppr
instance Show Pred    where show = render . ppr
instance Show Term    where show = render . ppr
instance Show VName   where show = render . ppr
-}