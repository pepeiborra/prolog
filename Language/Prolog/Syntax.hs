{-# LANGUAGE StandaloneDeriving, FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Prolog.Syntax where

import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Traversable

import Text.PrettyPrint as Ppr

type Program = [Clause]
data ClauseF f = f :- [f] deriving (Eq, Show)
data PredF f   = Pred Atom [f] | Cut  deriving (Eq, Show)
data TermF f = Term Atom [f] | Int Integer | Float Double | Var VName | Wildcard deriving (Eq, Show)
data In f = In {out::f (In f)}

type Clause = ClauseF Pred
type Pred   = PredF Term
type Term   = In TermF
data VName  = VName String | Auto Int deriving (Eq, Show)
type Atom   = String

atom :: Atom -> Term
atom f = term f []

term :: Atom -> [Term] -> Term
term f = In . Term f

var :: Atom -> Term
var  = In . Var . VName

var' :: Int -> Term
var' = In . Var . Auto

int = In . Int
float = In . Float
wildcard = In Wildcard

subterms :: Term -> [Term]
subterms (In t) = In t : Prelude.concat (subterms <$> toList t)

vars :: Term -> [VName]
vars t = [ v | (out -> Var v) <- subterms t] where
    isVar (out -> Var{}) = True
    isVar _              = False


deriving instance Eq (f(In f)) => Eq (In f)
deriving instance Show (f(In f)) => Show (In f)

class Ppr a where ppr :: a -> Doc
instance Ppr a => Ppr (TermF a) where
    ppr (Var v)  = ppr v
    ppr (Term f []) = text f
    ppr (Term f tt) = text f <> parens (fcat (punctuate comma $ map ppr tt))
    ppr (Int i)     = Ppr.integer i
    ppr (Float i)   = double i
    ppr Wildcard    = char '_'

instance Ppr VName where
    ppr (VName v)  = text v
    ppr (Auto v_i) = text "V" <> Ppr.int v_i

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


-- Functor boilerplate
-- --------------------
instance Functor     ClauseF where fmap     f (h :- c) = f h :- fmap f c
instance Foldable    ClauseF where foldMap  f (h :- c) = f h `mappend` foldMap f c
instance Traversable ClauseF where traverse f (h :- c) = (:-) <$> f h <*> traverse f c

instance Functor     PredF where
    fmap     f (Pred a tt) = Pred a (fmap f tt)
    fmap     f Cut         = Cut
instance Foldable    PredF where
    foldMap  f (Pred a tt) = foldMap f tt
    foldMap  f Cut         = mempty
instance Traversable PredF where
    traverse f (Pred a tt) = Pred a <$> traverse f tt
    traverse f Cut         = pure Cut

instance Functor TermF     where
    fmap     f (Term a tt) = Term a (fmap f tt)
    fmap     f (Var i)     = Var i
    fmap     f (Int i)     = Int i
    fmap     f (Float d)   = Float d
    fmap     f Wildcard    = Wildcard
instance Foldable    TermF where
    foldMap  f (Term a tt) = foldMap f tt
    foldMap  f _           = mempty
instance Traversable TermF where
    traverse f (Term a tt) = Term a <$> traverse f tt
    traverse f (Var i)     = pure (Var i)
    traverse f (Int i)     = pure (Int i)
    traverse f (Float i)   = pure (Float i)
    traverse f Wildcard    = pure Wildcard
