{-# LANGUAGE StandaloneDeriving, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Language.Prolog.Syntax (
     ClauseF(..), GoalF(..), TermF(..),
     Program, Clause, Goal, Term,
     Program', Clause', Goal', Term',
     Program'', Clause'',
     ident, term, tuple, var, var',
     cons, nil, int, float, string, wildcard,
     GetVars(..),
     mapTermId, mapPredId,
     Ppr(..)
     ) where

import Control.Applicative
import Control.Monad.Free
import Data.Foldable
import Data.Monoid
import qualified Data.Set as Set
import Data.Term hiding (Term)
import Data.Term.Var
import Data.Traversable as T

import Text.PrettyPrint hiding (int, float)
import qualified Text.PrettyPrint as Ppr

data ClauseF f = f :- [f] deriving (Eq, Ord, Show)
data GoalF id f= Pred {pred::id,args::[f]}
               | f :=: f
               | Is f f
               | Cut
   deriving (Eq, Ord, Show)
data TermF id f= Term {functor::id, fargs::[f]}
               | Cons f f
               | Nil
               | Tuple [f]
               | Int Integer
               | Float Double
               | String String
               | Wildcard deriving (Eq, Ord, Show)

type Program'' id term = [Clause'' id term]
type Clause''  id term = ClauseF (GoalF id term)

type Program' id var = Program'' id (Term' id var)
type Clause'  id var = Clause''  id (Term' id var)
type Goal'    id var = GoalF     id (Term' id var)
type Term'    id var = Free (TermF id) var

type Program id = [Clause id]
type Clause  id = ClauseF (Goal id)
type Goal    id = GoalF id (Term id)
type Term    id = Term' id Var

ident :: id -> Term' id a
ident f = term f []

term :: id -> [Term' id a] -> Term' id a
term f = Impure . Term f

tuple :: [Term' id a] -> Term' id a
tuple = Impure . Tuple

cons :: (term ~ Free (TermF id) var) => term -> term -> term
cons = (Impure.) . Cons

nil :: (term ~ Free (TermF id) var) => term
nil = Impure Nil

int      = Impure . Int
float    = Impure . Float
string   = Impure . String
wildcard = Impure Wildcard

class Ord var => GetVars var t | t -> var where getVars :: t -> [var]
instance GetVars Var Var where getVars v = [v]
instance (Functor termF, Foldable termF, Ord var) => GetVars var (Free termF var) where getVars = snub . toList
instance (GetVars var t, Foldable f) => GetVars var (f t) where getVars = snub . foldMap getVars
--instance (GetVars t var, Foldable f, Foldable g) => GetVars (g(f t)) var where getVars = (foldMap.foldMap) getVars

mapTermId :: (id -> id') -> TermF id a -> TermF id' a
mapTermId f (Term id a) = Term (f id) a
mapTermId _ (Tuple tt)  = Tuple tt
mapTermId _ (Int i)     = Int i
mapTermId _ (Float f)   = Float f
mapTermId _ (String s)  = String s
mapTermId _ Wildcard    = Wildcard

mapPredId f (Pred id tt) = Pred (f id) tt
mapPredId _ (Is t1 t2)   = Is t1 t2
mapPredId _ (t1 :=: t2)  = t1 :=: t2
mapPredId _ Cut          = Cut

class Ppr a where ppr :: a -> Doc

--instance (Ppr a, Ppr id) => Ppr (TermF id a) where
instance (Ppr id, Ppr v) => Ppr (TermF id (Free (TermF id) v)) where
    ppr (Term f []) = ppr f
    ppr (Term f tt) = ppr f <> parens (hcat (punctuate comma $ map ppr tt))
    ppr (Tuple tt ) = parens (hcat (punctuate comma $ map ppr tt))
    ppr (Cons h t)
        | Just elems <- getElems t = brackets (hcat $ punctuate comma $ map ppr (h:elems))
        | otherwise   = brackets (ppr h <> text "|" <> ppr t)
      where getElems (Impure Nil) = Just []
            getElems (Impure (Cons a b)) = (a :) `fmap` getElems b
            getElems _ = Nothing
    ppr Nil         = brackets (Ppr.empty)
    ppr (Int i)     = Ppr.integer i
    ppr (Float i)   = double i
    ppr Wildcard    = char '_'

instance Ppr Var where
    ppr (VName v)  = text v
    ppr (VAuto v_i) = text "V" <> Ppr.int v_i

instance (Ppr idp, Ppr term) => Ppr (GoalF idp term) where
    ppr (Pred f []) = ppr f
    ppr (Pred f tt) = ppr f <> parens(hcat (punctuate comma $ map ppr tt))
    ppr Cut         = text "!"
    ppr (a `Is` b)  = ppr a <+> text "is" <+> ppr b
    ppr (a :=: b)  = ppr a <+> text "=" <+> ppr b

instance (Ppr (f(Free f a)), Ppr a) => Ppr (Free f a) where ppr (Impure t) = ppr t; ppr (Pure a) = ppr a
instance Ppr a => Ppr (ClauseF a)  where
    ppr (h :- []) = ppr h <> char '.'
    ppr (h :- t) = ppr h <+> text ":-" <+> hcat(punctuate comma (map ppr t)) <> char '.'

instance (Ppr idp, Ppr term) => Ppr (Program'' idp term) where ppr = vcat . map ppr

--instance Ppr Char where ppr = char
instance Ppr String where ppr = text
instance Ppr Int    where ppr = Ppr.int
instance Ppr a => Ppr (Maybe a) where
    ppr Nothing  = text "Nothing"
    ppr (Just a) = text "Just" <+> ppr a
instance Ppr a => Ppr [a]     where ppr = brackets . hcat . punctuate comma . map ppr
instance (Ppr a, Ppr b) => Ppr (a,b) where ppr (a,b) = parens (ppr a <> comma <> ppr b)
instance (Ppr a, Ppr b, Ppr c) => Ppr (a,b,c) where ppr (a,b,c) = parens (ppr a <> comma <> ppr b <> comma <> ppr c)
instance (Ppr a, Ppr b, Ppr c, Ppr d) => Ppr (a,b,c,d) where
    ppr (a,b,c,d) = parens (fsep $ punctuate comma [ppr a, ppr b, ppr c, ppr d])

--instance Ppr String where ppr = text

{-
instance Show Program where show = render . ppr
instance Show Clause  where show = render . ppr
instance Show Goal    where show = render . ppr
instance Show Term    where show = render . ppr
instance Show VName   where show = render . ppr
-}


-- Functor boilerplate
-- --------------------
instance Functor     ClauseF where fmap     f (h :- c) = f h :- fmap f c
instance Foldable    ClauseF where foldMap  f (h :- c) = f h `mappend` foldMap f c
instance Traversable ClauseF where traverse f (h :- c) = (:-) <$> f h <*> traverse f c

instance Functor     (GoalF id) where
    fmap     f (Pred a tt) = Pred a (fmap f tt)
    fmap     f Cut         = Cut
    fmap     f (Is a b)    = Is (f a) (f b)
    fmap     f (a :=: b)   = f a :=: f b
instance Foldable    (GoalF id) where
    foldMap  f (Pred a tt) = foldMap f tt
    foldMap  f Cut         = mempty
    foldMap  f (Is a b)    = f a `mappend` f b
    foldMap  f (a :=: b)   = f a `mappend` f b
instance Traversable (GoalF id) where
    traverse f (Pred a tt) = Pred a <$> traverse f tt
    traverse f Cut         = pure Cut
    traverse f (Is a b)    = Is    <$> f a <*> f b
    traverse f (a :=: b)   = (:=:) <$> f a <*> f b

instance Functor (TermF id) where
    fmap     f (Term a tt) = Term a (fmap f tt)
    fmap     f (Tuple  tt) = Tuple  (fmap f tt)
    fmap     f (Cons h t)  = Cons (f h) (f t)
    fmap     _ Nil         = Nil
    fmap     f (Int i)     = Int i
    fmap     f (Float d)   = Float d
    fmap     f Wildcard    = Wildcard
instance Foldable (TermF id) where
    foldMap  f (Term a tt) = foldMap f tt
    foldMap  f (Tuple  tt) = foldMap f tt
    foldMap  f (Cons h t)  = f h `mappend` f t
    foldMap  f _           = mempty
instance Traversable (TermF id) where
    traverse f (Term a tt) = Term a <$> traverse f tt
    traverse f (Tuple  tt) = Tuple  <$> traverse f tt
    traverse f (Cons h t)  = Cons <$> f h <*> f t
    traverse _ Nil         = pure Nil
    traverse f (Int i)     = pure (Int i)
    traverse f (Float i)   = pure (Float i)
    traverse f Wildcard    = pure Wildcard

-- Other
-- -----
snub :: Ord a => [a] -> [a]
snub = Set.toList . Set.fromList