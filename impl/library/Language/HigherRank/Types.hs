{-# LANGUAGE DeriveGeneric, MultiParamTypeClasses, FlexibleInstances #-}

module Language.HigherRank.Types where

import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)


type TmName = Name Expr
type TyName = Name Type

--------------------------------------------------------------------------------
-- Expressions

data Expr
  = EUnit
  | EVar TmName
  | EAnn Expr Type
  | ELam (Bind TmName Expr)
  | ELamA (Bind (TmName, Embed Type) Expr)
  | ELet (Bind (TmName, Embed Expr) Expr)
  | EApp Expr Expr
  | LitV Double
  | Add Expr Expr
  | ETrue
  | EFalse
  deriving (Show, Generic)


ebind :: String -> Expr -> Bind TmName Expr
ebind n = bind (s2n n)

elam :: String -> Expr -> Expr
elam b e = ELam (bind (s2n b) e)

elamA :: (String, Type) -> Expr -> Expr
elamA (x, t) e = ELamA (bind (s2n x, embed t) e)


evar :: String -> Expr
evar = EVar . s2n


elet :: String -> Expr -> Expr -> Expr
elet s e b = ELet (bind (s2n s, embed e) b)


--------------------------------------------------------------------------------
-- Types

data ETVar
  = ETS TyName
  | ETG TyName
  deriving (Show, Generic, Eq)


isETS :: ETVar -> Bool
isETS (ETS _) = True
isETS _ = False


data Type
  = TUnit
  | TNum
  | TUnknown
  | TVar TyName
  | TEVar ETVar
  | TArr Type Type
  | TAll (Bind TyName Type)
  | TBool
  deriving (Show, Generic)


tvar :: String -> Type
tvar = TVar . s2n

tforall :: String -> Type -> Type
tforall t b = TAll (bind (s2n t) b)


-------------------------------------------------------
-- Unbound library instances

instance Alpha Expr
instance Alpha Type
instance Alpha ETVar

instance Subst Expr Type
instance Subst Expr ETVar
instance Subst Type ETVar

instance Subst Expr Expr where
  isvar (EVar v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Type Type where
  isvar (TVar v) = Just (SubstName v)
  isvar _ = Nothing
