{-# LANGUAGE StandaloneDeriving, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Language.Prolog.Syntax (
     ClauseF(..), cHead, cBody, GoalF(..), TermF(..),
     Program, Clause, Goal, Term,
     Program', Clause', Goal', Term',
     Program'', Clause'',
     ProgramI,  ClauseI,
     ident, term, tuple, var, var',
     cons, nil, int, float, string, wildcard,
     mapPredId,
     Pretty(..)
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
import Data.Traversable (Traversable, traverse)

import Text.PrettyPrint.HughesPJClass hiding (int, float)
import qualified Text.PrettyPrint.HughesPJClass as Ppr

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

type ProgramI idp idt = [ClauseI idp idt]
type ClauseI  idp idt =  ClauseF (GoalF idp (Term' idt Var))

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

cHead :: ClauseF a -> a
cBody :: ClauseF a -> [a]

cHead (h :- _) = h
cBody (_ :- b) = b

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

instance (Pretty id, Pretty a) => Pretty (TermF id a) where
    pPrint (Term f []) = pPrint f
    pPrint (Term f tt) = pPrint f <> parens (hcat (punctuate comma $ map pPrint tt))
    pPrint (Tuple tt ) = parens (hcat (punctuate comma $ map pPrint tt))
    pPrint (Cons h t)  = brackets (pPrint h <> text "|" <> pPrint t)
    pPrint Nil         = brackets (Ppr.empty)
    pPrint (Int i)     = pPrint i
    pPrint (Float i)   = double i
    pPrint Wildcard    = char '_'

instance (Pretty a) => Pretty (TermF String a) where
    pPrint (Term f []) = pPrintS f
    pPrint (Term f tt) = pPrintS f <> parens (hcat (punctuate comma $ map pPrint tt))
    pPrint (Tuple tt ) = parens (hcat (punctuate comma $ map pPrint tt))
    pPrint (Cons h t)  = brackets (pPrint h <> text "|" <> pPrint t)
    pPrint Nil         = brackets (Ppr.empty)
    pPrint (Int i)     = pPrint i
    pPrint (Float i)   = double i
    pPrint Wildcard    = char '_'

instance (Pretty id, Pretty (Free (TermF id) v)) => Pretty (TermF id (Free (TermF id) v)) where
    pPrint (Term f []) = pPrint f
    pPrint (Term f tt) = pPrint f <> parens (hcat (punctuate comma $ map pPrint tt))
    pPrint (Tuple tt ) = parens (hcat (punctuate comma $ map pPrint tt))
    pPrint (Cons h t)
        | Just elems <- getElems t = brackets (hcat $ punctuate comma $ map pPrint (h:elems))
        | otherwise   = brackets (pPrint h <> text "|" <> pPrint t)
      where getElems (Impure Nil) = Just []
            getElems (Impure (Cons a b)) = (a :) `fmap` getElems b
            getElems _ = Nothing
    pPrint Nil         = brackets (Ppr.empty)
    pPrint (Int i)     = pPrint i
    pPrint (Float i)   = double i
    pPrint Wildcard    = char '_'

instance (Pretty (Term' String v)) => Pretty (TermF String (Term' String v)) where
    pPrint (Term f []) = pPrintS f
    pPrint (Term f tt) = pPrintS f <> parens (hcat (punctuate comma $ map pPrint tt))
    pPrint (Tuple tt ) = parens (hcat (punctuate comma $ map pPrint tt))
    pPrint (Cons h t)
        | Just elems <- getElems t = brackets (hcat $ punctuate comma $ map pPrint (h:elems))
        | otherwise   = brackets (pPrint h <> text "|" <> pPrint t)
      where getElems (Impure Nil) = Just []
            getElems (Impure (Cons a b)) = (a :) `fmap` getElems b
            getElems _ = Nothing
    pPrint Nil         = brackets (Ppr.empty)
    pPrint (Int i)     = pPrint i
    pPrint (Float i)   = double i
    pPrint Wildcard    = char '_'

pPrintS string = if any isSpace string then quotes (text string) else text string

instance (Pretty idp, Pretty term) => Pretty (GoalF idp term) where
    pPrint (Pred f []) = pPrint f
    pPrint (Pred f tt) = pPrint f <> parens(hcat (punctuate comma $ map pPrint tt))
    pPrint Cut         = text "!"
    pPrint (a `Is` b)  = pPrint a <+> text "is" <+> pPrint b
    pPrint (a :=: b)  = pPrint a <+> text "=" <+> pPrint b

instance (Pretty term) => Pretty (GoalF String term) where
    pPrint (Pred f []) = pPrintS f
    pPrint (Pred f tt) = pPrintS f <> parens(hcat (punctuate comma $ map pPrint tt))
    pPrint Cut         = text "!"
    pPrint (a `Is` b)  = pPrint a <+> text "is" <+> pPrint b
    pPrint (a :=: b)  = pPrint a <+> text "=" <+> pPrint b

instance Pretty a => Pretty (ClauseF a)  where
    pPrint (h :- []) = pPrint h <> char '.'
    pPrint (h :- t)  = pPrint h <+> text ":-" <+> hcat(punctuate comma (map pPrint t)) <> char '.'
    pPrintList l     = vcat . map pPrint


-- Functor boilerplate
-- --------------------
instance Functor     ClauseF where fmap     f (h :- c) = f h :- fmap f c
instance Foldable    ClauseF where foldMap  f (h :- c) = f h `mappend` foldMap f c
instance Traversable ClauseF where traverse f (h :- c) = (:-) <$> f h <*> traverse f c

instance BifunctorM GoalF where
    bimapM fid f (Pred a tt) = liftM2 Pred (fid a) (mapM f tt)
    bimapM fid f Cut         = return Cut
    bimapM fid f (Is a b)    = liftM2 Is (f a) (f b)
    bimapM fid f (a :=: b)   = liftM2 (:=:) (f a) (f b)
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

instance BifunctorM TermF where
    bimapM fid f (Term a tt) = liftM2 Term (fid a) (mapM f tt)
    bimapM _   f (Tuple  tt) = Tuple `liftM` mapM f tt
    bimapM _   f (Cons h t)  = liftM2 Cons (f h) (f t)
    bimapM _   _ Nil         = return Nil
    bimapM _   _ (Int i)     = return $ Int i
    bimapM _   _ (Float d)   = return $ Float d
    bimapM _   _ Wildcard    = return Wildcard
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

instance Ord id => HasId (TermF id) where
    type TermId (TermF id) = id
    getId (Term id _) = Just id
    getId _           = Nothing

instance (HasId termF, TermId termF ~ id, Ord id, Foldable termF) => HasSignature (Program'' id (Free termF v)) where
  type SignatureId (Program'' id (Free termF v)) = id
  getSignature cc = Sig {constructorSymbols = aritiesF, definedSymbols = aritiesP}
   where
    aritiesP = Map.fromList [ (f, length tt) | Pred f tt   <- F.toList =<< cc]
    aritiesF = Map.fromList [ (f, length $ toList t) | Pred _ args <- F.toList =<< cc, Impure t <- subterms =<< args, Just f <- [getId t]]

instance (HasId termF, TermId termF ~ id, Ord id, Foldable termF) =>
    HasSignature (ClauseF (GoalF id (Free termF v))) where
  type SignatureId (ClauseF (GoalF id (Free termF v))) = id
  getSignature c = getSignature [c]

-- Other
-- -----
snub :: Ord a => [a] -> [a]
snub = Set.toList . Set.fromList