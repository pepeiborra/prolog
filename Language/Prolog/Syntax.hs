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
     mapPredId,
     Ppr(..)
     ) where

import Control.Applicative
import Control.Monad.Free
import Data.Bifunctor
import Data.Char
import Data.Foldable as F (Foldable(..), toList)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Term hiding (Term)
import Data.Term.Rules
import Data.Term.Var
import Data.Term.Ppr
import Data.Traversable as T

import Text.PrettyPrint hiding (int, float)
import qualified Text.PrettyPrint as Ppr

data ClauseF f = f :- [f] deriving (Eq, Ord, Show)
data GoalF id f= Pred {pred::id,args::[f]}
               | f :=: f
               | Is f f
               | Ifte f f f
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

mapTermId :: (id -> id') -> TermF id a -> TermF id' a
mapTermId f = bimap f id
mapPredId f = bimap f id

instance (Ppr id, Ppr a) => Ppr (TermF id a) where
    ppr (Term f []) = ppr f
    ppr (Term f tt) = ppr f <> parens (hcat (punctuate comma $ map ppr tt))
    ppr (Tuple tt ) = parens (hcat (punctuate comma $ map ppr tt))
    ppr (Cons h t)  = brackets (ppr h <> text "|" <> ppr t)
    ppr Nil         = brackets (Ppr.empty)
    ppr (Int i)     = Ppr.integer i
    ppr (Float i)   = double i
    ppr Wildcard    = char '_'

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

instance Ppr v => Ppr (TermF String (Term' String v)) where
    ppr (Term f []) = pprS f
    ppr (Term f tt) = pprS f <> parens (hcat (punctuate comma $ map ppr tt))
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

pprS string = if any isSpace string then quotes (text string) else text string

instance (Ppr idp, Ppr term) => Ppr (GoalF idp term) where
    ppr (Pred f []) = ppr f
    ppr (Pred f tt) = ppr f <> parens(hcat (punctuate comma $ map ppr tt))
    ppr Cut         = text "!"
    ppr (a `Is` b)  = ppr a <+> text "is" <+> ppr b
    ppr (a :=: b)  = ppr a <+> text "=" <+> ppr b

instance Ppr a => Ppr (ClauseF a)  where
    ppr (h :- []) = ppr h <> char '.'
    ppr (h :- t) = ppr h <+> text ":-" <+> hcat(punctuate comma (map ppr t)) <> char '.'

instance (Ppr idp, Ppr term) => Ppr (Program'' idp term) where ppr = vcat . map ppr

-- Functor boilerplate
-- --------------------
instance Functor     ClauseF where fmap     f (h :- c) = f h :- fmap f c
instance Foldable    ClauseF where foldMap  f (h :- c) = f h `mappend` foldMap f c
instance Traversable ClauseF where traverse f (h :- c) = (:-) <$> f h <*> traverse f c

instance Bifunctor GoalF where
    bimap fid f (Pred a tt) = Pred (fid a) (fmap f tt)
    bimap fid f Cut         = Cut
    bimap fid f (Is a b)    = Is (f a) (f b)
    bimap fid f (a :=: b)   = f a :=: f b
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

instance Bifunctor TermF where
    bimap fid f (Term a tt) = Term (fid a) (fmap f tt)
    bimap _   f (Tuple  tt) = Tuple  (fmap f tt)
    bimap _   f (Cons h t)  = Cons (f h) (f t)
    bimap _   _ Nil         = Nil
    bimap _   _ (Int i)     = Int i
    bimap _   _ (Float d)   = Float d
    bimap _   _ Wildcard    = Wildcard
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

-- Term Boilerplate
-- ----------------
instance (Eq id, GetMatcher t v a) => GetMatcher t v (GoalF id a) where getMatcherM = getMatcherMdefault
instance (Eq id, GetUnifier t v a) => GetUnifier t v (GoalF id a) where getUnifierM = getUnifierMdefault
instance         GetFresh t v a    => GetFresh   t v (GoalF id a) where getFreshM   = getFreshMdefault

instance GetMatcher t v a => GetMatcher t v (ClauseF a) where getMatcherM = getMatcherMdefault
instance GetUnifier t v a => GetUnifier t v (ClauseF a) where getUnifierM = getUnifierMdefault
instance GetFresh t v a   => GetFresh   t v (ClauseF a) where getFreshM   = getFreshMdefault


instance HasId (TermF id) id where getId (Term id _) = Just id
                                   getId _           = Nothing

instance (Show id, Ord id) => HasSignature (Program' id var) id where
  getSignature cc = let aritiesP = Map.fromList [ (f, length tt) | Pred f tt   <- F.toList =<< cc]
                        aritiesF = Map.fromList [ (f, length tt) | Pred _ args <- F.toList =<< cc, Impure(Term f tt) <- subterms =<< args ]
                        functors = Map.keysSet aritiesF
                        preds    = Map.keysSet aritiesP
                        in Sig {constructorSymbols = functors, definedSymbols = preds, arity = aritiesP `mappend` aritiesF}

-- Other
-- -----
snub :: Ord a => [a] -> [a]
snub = Set.toList . Set.fromList