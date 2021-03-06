{-# LANGUAGE StandaloneDeriving, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns, PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Language.Prolog.Syntax (
     ClauseF(..), cHead, cBody, GoalF(..), TermF(..),
     Program, Clause, Goal, Term,
     Program', Clause', Goal', Term',
     Program'', Clause'',
     ProgramI,  ClauseI,
     goalToTerm, termToGoal,
     ident, term, tuple, var, var',
     cons, nil, int, float, string, wildcard,
     mapPredId,
     Pretty(..)
     ) where

import Control.Applicative
import Control.Applicative.Compose
import Control.Monad.Free
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Char
import Data.Foldable as F (Foldable(..), toList)
import Data.Monoid (Monoid(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Term hiding (Term, TermF, Var)
import qualified Data.Term as Family
import Data.Term.Rules
import Data.Term.Var
import Data.Traversable (Traversable, traverse)
import Prelude.Extras

import Text.PrettyPrint.HughesPJClass hiding (int, float)
import qualified Text.PrettyPrint.HughesPJClass as Ppr

data ClauseF f = f :- [f] deriving (Eq, Ord, Show)
data GoalF id f= Pred {pred::id,args::[f]}
               | f :=: f
               | Is f f
               | Ift  f (GoalF id f)
               | Ifte f (GoalF id f) (GoalF id f)
               | Not (GoalF id f)
               | Cut
                 deriving (Eq, Ord, Show)

data TermF id f= Term {functor::id, fargs::[f]}
               | Cons f f
               | Nil
               | Tuple [f]
               | Int Integer
               | Float Double
               | String String
               | Wildcard
                 deriving (Eq, Ord, Show)

instance Eq1 ClauseF where f :- ff ==# g :- gg = f == g && ff == gg

instance Eq id => Eq1(GoalF id)
instance Eq id => Eq1(TermF id)
instance Ord id => Ord1(GoalF id)
instance Ord id => Ord1(TermF id)
instance Show id => Show1(GoalF id)
instance Show id => Show1(TermF id)


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

instance Applicative ClauseF where
  pure x = x :- [x]
  f :- gg <*> x :- yy = f x :- zipWith ($) gg yy

pattern CJ x = (Compose(Just x))
pattern CN   = Compose Nothing

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

goalToTerm :: GoalF id (Term' id var) -> Maybe(Term' id var)
goalToTerm (Pred f tt) = Just(term f tt)
goalToTerm _g = const Nothing _g

termToGoal (Impure (Term f tt)) = Just [(Pred f tt)]
termToGoal (Impure (Tuple tt))  = liftM concat $ mapM termToGoal tt
termToGoal _t = Nothing

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
    pPrint (Not t)     = text "\\+" <+> pPrint t
    pPrint (Ifte c t e)= pPrint c <+> text "->" <+> pPrint t <+> text ";" <+> pPrint e
    pPrint (Ift c t)   = pPrint c <+> text "->" <+> pPrint t
    pPrint (a `Is` b)  = pPrint a <+> text "is" <+> pPrint b
    pPrint (a :=: b)   = pPrint a <+> text "=" <+> pPrint b

instance (Pretty term) => Pretty (GoalF String term) where
    pPrint (Pred f []) = pPrintS f
    pPrint (Pred f tt) = pPrintS f <> parens(hcat (punctuate comma $ map pPrint tt))
    pPrint Cut         = text "!"
    pPrint (Not t)     = text "\\+" <+> pPrint t
    pPrint (a `Is` b)  = pPrint a <+> text "is" <+> pPrint b
    pPrint (a :=: b)   = pPrint a <+> text "=" <+> pPrint b
    pPrint (Ifte c t e)= pPrint c <+> text "->" <+> pPrint t <+> text ";" <+> pPrint e
    pPrint (Ift c t)   = pPrint c <+> text "->" <+> pPrint t

instance Pretty a => Pretty (ClauseF a)  where
    pPrint (h :- []) = pPrint h <> char '.'
    pPrint (h :- t)  = pPrint h <+> text ":-" <+> hcat(punctuate comma (map pPrint t)) <> char '.'
    pPrintList l     = vcat . map pPrint

-- Term Families
-- -------------
type instance Family.Var   (ClauseF a) = Family.Var a
type instance Family.TermF (ClauseF a) = Family.TermF a

type instance Family.Var   (GoalF id a) = Family.Var a
type instance Family.TermF (GoalF id a) = Family.TermF a

type instance Family.Id  (TermF id)   = id
type instance Family.Id  (ClauseF a)  = Family.Id a
type instance Family.Id  (GoalF id a) = id

-- Functor boilerplate
-- --------------------
instance Functor     ClauseF where fmap     f (h :- c) = f h :- fmap f c
instance Foldable    ClauseF where foldMap  f (h :- c) = f h `mappend` foldMap f c
instance Traversable ClauseF where traverse f (h :- c) = (:-) <$> f h <*> traverse f c

instance Bifunctor GoalF where bimap = bimapDefault
instance Bifoldable GoalF where bifoldMap = bifoldMapDefault
instance Bitraversable GoalF where
    bitraverse fid f (Pred a tt) = liftA2 Pred (fid a) (traverse f tt)
    bitraverse fid f Cut         = pure Cut
    bitraverse fid f (Not t)     = liftA  Not (bitraverse fid f t)
    bitraverse fid f (Is a b)    = liftA2 Is (f a) (f b)
    bitraverse fid f (a :=: b)   = liftA2 (:=:) (f a) (f b)
    bitraverse fid f (Ifte a b c)= liftA3 Ifte (f a) (bitraverse fid f b) (bitraverse fid f c)
    bitraverse fid f (Ift  a b)  = liftA2 Ift  (f a) (bitraverse fid f b)

deriving instance Functor  (GoalF id)
deriving instance Foldable (GoalF id)
deriving instance Traversable (GoalF id)

instance Bifunctor TermF where bimap = bimapDefault
instance Bifoldable TermF where bifoldMap = bifoldMapDefault
instance Bitraversable TermF where
    bitraverse fid f (Term a tt) = liftA2 Term (fid a) (traverse f tt)
    bitraverse _   f (Tuple  tt) = Tuple `liftA` traverse f tt
    bitraverse _   f (Cons h t)  = liftA2 Cons (f h) (f t)
    bitraverse _   _ Nil         = pure Nil
    bitraverse _   _ (Int i)     = pure $ Int i
    bitraverse _   _ (Float d)   = pure $ Float d
    bitraverse _   _ Wildcard    = pure Wildcard

deriving instance Functor (TermF id)
deriving instance Foldable (TermF id)
deriving instance Traversable (TermF id)

instance Eq id => Applicative (Maybe :+: TermF id) where
  pure _ = CN
  CJ(Term i ff) <*> CJ(Term id' xx)
    | i == id' = CJ(Term i (zipWith ($) ff xx))
  CJ(Cons f g) <*> CJ(Cons x y) = CJ(Cons (f x) (g y))
  CJ Nil <*> CJ Nil = CJ Nil
  CJ(Tuple ff) <*> CJ(Tuple xx) = CJ(Tuple $ zipWith ($) ff xx)
  CJ(Int i) <*> CJ(Int j) | i == j = CJ(Int i)
  CJ(Float i) <*> CJ(Float j) | i == j = CJ(Float i)
  CJ(String s) <*> CJ(String s') | s == s' = CJ(String s)
  CJ Wildcard <*> CJ Wildcard = CJ Wildcard
  _ <*> _ = CN

instance Eq id => Applicative (Maybe :+: GoalF id) where
  pure _ = CN
  CJ (Pred i ff) <*> CJ(Pred id' xx)
    | i == id' = CJ $ Pred i (zipWith ($) ff xx)
  CJ(f :=: g) <*> CJ(x :=: y) = CJ (f x :=: g y)
  CJ(Is f g)  <*> CJ(Is x y) = CJ (Is (f x) (g y))
  CJ(Ift f k) <*> CJ(Ift x k') = Compose $ do
    kk' <- decompose(CJ k <*> CJ k')
    return (Ift (f x) kk')
  CJ(Ifte f k1 k2) <*> CJ(Ifte x k1' k2') = Compose $ do
    kk1 <- decompose(CJ k1 <*> CJ k1')
    kk2 <- decompose(CJ k2 <*> CJ k2')
    return (Ifte (f x) kk1 kk2)
  CJ(Not k) <*> CJ(Not k') = Compose(Not <$> decompose(CJ k <*> CJ k'))
  CJ Cut <*> CJ Cut = CJ Cut
  _ <*> _ = CN

-- Term Boilerplate
-- ----------------
instance GetVars f => GetVars (GoalF id f) where getVars = foldMap getVars

instance (Eq id, GetMatcher a) => GetMatcher (GoalF id a) where getMatcherM = getMatcherMdefault
instance (Eq id, GetUnifier a) => GetUnifier (GoalF id a) where getUnifierM = getUnifierMdefault
instance         GetFresh a    => GetFresh   (GoalF id a) where getFreshM   = getFreshMdefault

instance GetMatcher  a  => GetMatcher (ClauseF a) where getMatcherM = getMatcherMdefault
instance (GetUnifier a) => GetUnifier (ClauseF a) where getUnifierM = getUnifierMdefault
instance GetFresh    a  => GetFresh   (ClauseF a) where getFreshM   = getFreshMdefault

instance Ord id => HasId1 (TermF id) where
    getId1 (Term id _) = Just id
    getId1 _           = Nothing

instance (HasId1 termF, Family.Id termF ~ id, Ord id, Foldable termF) => HasSignature (Program'' id (Free termF v)) where
  getSignature cc = Sig {constructorSymbols = aritiesF, definedSymbols = aritiesP}
   where
    aritiesP = Map.fromList [ (f, length tt) | Pred f tt   <- F.toList =<< cc]
    aritiesF = Map.fromList [ (f, length $ toList t) | Pred _ args <- F.toList =<< cc, Impure t <- subterms =<< args, Just f <- [getId1 t]]

instance (HasId1 termF, Family.Id termF ~ id, Ord id, Foldable termF) =>
    HasSignature (ClauseF (GoalF id (Free termF v))) where
  getSignature c = getSignature [c]

-- Other
-- -----
snub :: Ord a => [a] -> [a]
snub = Set.toList . Set.fromList
