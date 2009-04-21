{-# LANGUAGE StandaloneDeriving, FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverlappingInstances #-}
module Language.Prolog.Syntax where

import Control.Applicative
import Control.Monad.Free
import Data.Foldable
import Data.Monoid
import Data.Traversable as T

import Text.PrettyPrint as Ppr

data ClauseF f = f :- [f] deriving (Eq, Show)
data AtomF id f= Pred {pred::id,args::[f]}
               | f :=: f
               | Is f f
               | Cut deriving (Eq, Show)
data TermF id f= Term {functor::id, fargs::[f]}
               | Tuple [f]
               | Int Integer
               | Float Double
               | String String
               | Wildcard deriving (Eq, Show)

data VName  = VName String | Auto Int deriving (Eq, Show)

type Program'' id term = [Clause'' id term]
type Clause''  id term = ClauseF (AtomF id term)

type Program' id var = Program'' id (Term' id var)
type Clause'  id var = Clause''  id (Term' id var)
type Atom'    id var = AtomF     id (Term' id var)
type Term'    id var = Free (TermF id) var

type Program id = [Clause id]
type Clause  id = ClauseF (Atom id)
type Atom    id = AtomF id (Term id)
type Term    id = Term' id VName

ident :: id -> Term' id a
ident f = term f []

term :: id -> [Term' id a] -> Term' id a
term f = Impure . Term f

tuple :: [Term' id a] -> Term' id a
tuple = Impure . Tuple

var :: String -> Term id
var  = return . VName

var' :: Int -> Term id
var' = return . Auto

int      = Impure . Int
float    = Impure . Float
string   = Impure . String
wildcard = Impure Wildcard

subterms :: Term' id a -> [Term' id a]
subterms (Impure t) = Impure t : Prelude.concat (subterms <$> toList t)
subterms _ = []

vars :: Term' id a -> [a]
vars = toList

class Ppr a where ppr :: a -> Doc
instance (Show id, Ppr a) => Ppr (TermF id a) where
    ppr (Term f []) = text (show f)
    ppr (Term f tt) = text (show f) <> parens (fcat (punctuate comma $ map ppr tt))
    ppr (Tuple tt ) = ppr (Term "" tt)
    ppr (Int i)     = Ppr.integer i
    ppr (Float i)   = double i
    ppr Wildcard    = char '_'

instance Ppr VName where
    ppr (VName v)  = text v
    ppr (Auto v_i) = text "V" <> Ppr.int v_i

instance (Show idp, Ppr term) => Ppr (AtomF idp term) where
    ppr (Pred f []) = text (show f)
    ppr (Pred f tt) = text (show f) <> parens(fcat (punctuate comma $ map ppr tt))
    ppr Cut         = text "!"
    ppr (a `Is` b)  = ppr a <+> text "is" <+> ppr b
    ppr (a :=: b)  = ppr a <+> text "=" <+> ppr b

instance (Ppr (f(Free f a)), Ppr a) => Ppr (Free f a) where ppr (Impure t) = ppr t; ppr (Pure a) = ppr a
instance Ppr a => Ppr (ClauseF a)  where
    ppr (h :- []) = ppr h <> char '.'
    ppr (h :- t) = ppr h <+> text ":-" <+> fcat(punctuate comma (map ppr t)) <> char '.'

instance (Show idp, Ppr term) => Ppr (Program'' idp term) where ppr = vcat . map ppr

--instance Ppr Char where ppr = char
instance Ppr String where ppr = text
instance Ppr a => Ppr [a]     where ppr = brackets . hcat . punctuate comma . map ppr
instance (Ppr a, Ppr b) => Ppr (a,b) where ppr (a,b) = parens (ppr a <> comma <> ppr b)
instance (Ppr a, Ppr b, Ppr c) => Ppr (a,b,c) where ppr (a,b,c) = parens (ppr a <> comma <> ppr b <> comma <> ppr c)

--instance Ppr String where ppr = text

{-
instance Show Program where show = render . ppr
instance Show Clause  where show = render . ppr
instance Show Atom    where show = render . ppr
instance Show Term    where show = render . ppr
instance Show VName   where show = render . ppr
-}


-- Functor boilerplate
-- --------------------
instance Functor     ClauseF where fmap     f (h :- c) = f h :- fmap f c
instance Foldable    ClauseF where foldMap  f (h :- c) = f h `mappend` foldMap f c
instance Traversable ClauseF where traverse f (h :- c) = (:-) <$> f h <*> traverse f c

instance Functor     (AtomF id) where
    fmap     f (Pred a tt) = Pred a (fmap f tt)
    fmap     f Cut         = Cut
    fmap     f (Is a b)    = Is (f a) (f b)
    fmap     f (a :=: b)   = f a :=: f b
instance Foldable    (AtomF id) where
    foldMap  f (Pred a tt) = foldMap f tt
    foldMap  f Cut         = mempty
    foldMap  f (Is a b)    = f a `mappend` f b
    foldMap  f (a :=: b)   = f a `mappend` f b
instance Traversable (AtomF id) where
    traverse f (Pred a tt) = Pred a <$> traverse f tt
    traverse f Cut         = pure Cut
    traverse f (Is a b)    = Is    <$> f a <*> f b
    traverse f (a :=: b)   = (:=:) <$> f a <*> f b

instance Functor (TermF id) where
    fmap     f (Term a tt) = Term a (fmap f tt)
    fmap     f (Tuple  tt) = Tuple  (fmap f tt)
    fmap     f (Int i)     = Int i
    fmap     f (Float d)   = Float d
    fmap     f Wildcard    = Wildcard
instance Foldable (TermF id) where
    foldMap  f (Term a tt) = foldMap f tt
    foldMap  f (Tuple  tt) = foldMap f tt
    foldMap  f _           = mempty
instance Traversable (TermF id) where
    traverse f (Term a tt) = Term a <$> traverse f tt
    traverse f (Tuple  tt) = Tuple  <$> traverse f tt
    traverse f (Int i)     = pure (Int i)
    traverse f (Float i)   = pure (Float i)
    traverse f Wildcard    = pure Wildcard

