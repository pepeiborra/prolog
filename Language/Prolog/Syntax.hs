{-# LANGUAGE StandaloneDeriving, FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DisambiguateRecordFields #-}
module Language.Prolog.Syntax where

import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Traversable as T

import Text.PrettyPrint as Ppr

type Program id= [Clause id]
data ClauseF f = f :- [f] deriving (Eq, Show)
data AtomF id f= Pred {pred::id,args::[f]}
               | f :=: f
               | Is f f
               | Cut deriving (Eq, Show)
data TermF id f= Term {functor::id, fargs::[f]}
               | Tuple [f]
               | Int Integer
               | Float Double
               | Var VName
               | String String
               | Wildcard deriving (Eq, Show)

data In f = In {out::f (In f)}

type Clause id = ClauseF (Atom id)
type Atom   id = AtomF id (Term id)
type Term   id = In (TermF id)
data VName  = VName String | Auto Int deriving (Eq, Show)

ident :: id -> Term id
ident f = term f []

term :: id -> [Term id] -> Term id
term f = In . Term f

tuple :: [Term id] -> Term id
tuple = In . Tuple

var :: String -> Term id
var  = In . Var . VName

var' :: Int -> Term id
var' = In . Var . Auto

int      = In . Int
float    = In . Float
string   = In . String
wildcard = In Wildcard

subterms :: Term id -> [Term id]
subterms (In t) = In t : Prelude.concat (subterms <$> toList t)

vars :: Term id -> [VName]
vars t = [ v | (out -> Var v) <- subterms t] where
    isVar (out -> Var{}) = True
    isVar _              = False

foldIn           :: Functor f => (f a -> a) -> In f -> a
foldIn f  (In t) = f    (fmap (foldIn f) t)
foldInM          :: (Traversable f, Monad m) => (f a -> m a) -> In f -> m a
foldInM f (In t) = f =<< T.mapM (foldInM f) t

deriving instance Eq (f(In f)) => Eq (In f)
deriving instance Show (f(In f)) => Show (In f)

class Ppr a where ppr :: a -> Doc
instance (Show id, Ppr a) => Ppr (TermF id a) where
    ppr (Var v)  = ppr v
    ppr (Term f []) = text (show f)
    ppr (Term f tt) = text (show f) <> parens (fcat (punctuate comma $ map ppr tt))
    ppr (Tuple tt ) = ppr (Term "" tt)
    ppr (Int i)     = Ppr.integer i
    ppr (Float i)   = double i
    ppr Wildcard    = char '_'

instance Ppr VName where
    ppr (VName v)  = text v
    ppr (Auto v_i) = text "V" <> Ppr.int v_i

instance Show id => Ppr (Atom id) where
    ppr (Pred f []) = text (show f)
    ppr (Pred f tt) = text (show f) <> parens(fcat (punctuate comma $ map ppr tt))
    ppr Cut         = text "!"
    ppr (a `Is` b)  = ppr a <+> text "is" <+> ppr b
    ppr (a :=: b)  = ppr a <+> text "=" <+> ppr b

instance Ppr (f(In f)) => Ppr (In f) where ppr (In t) = ppr t
instance Ppr a => Ppr (ClauseF a)  where
    ppr (h :- []) = ppr h <> char '.'
    ppr (h :- t) = ppr h <+> text ":-" <+> fcat(punctuate comma (map ppr t)) <> char '.'

instance Show id => Ppr (Program id) where ppr = vcat . map ppr

--instance Ppr String where ppr = text
--instance (Ppr a, Ppr b) => Ppr (a,b) where ppr = parens (ppr a <> comma <+> ppr b)


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
    fmap     f (Var i)     = Var i
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
    traverse f (Var i)     = pure (Var i)
    traverse f (Int i)     = pure (Int i)
    traverse f (Float i)   = pure (Float i)
    traverse f Wildcard    = pure Wildcard
