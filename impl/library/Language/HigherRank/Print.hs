{-# LANGUAGE FlexibleInstances, ExistentialQuantification, OverloadedStrings, RankNTypes #-}

module Language.HigherRank.Print
  ( pprint
  ) where


import           Data.Text.Prettyprint.Doc (Doc, (<+>), pretty, (<>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Unbound.Generics.LocallyNameless

import           Language.HigherRank.Types


instance Pretty.Pretty (Name a) where
  pretty v = pretty (show v)

type FDoc = Doc ()

class FPretty p where
  ppr :: (Applicative m, LFresh m) => p -> m FDoc

pprint :: FPretty a => a -> String
pprint a = show (runLFreshM (ppr a))

instance FPretty Expr where
  ppr EUnit = return "()"
  ppr EFalse = return "false"
  ppr ETrue = return "true"
  ppr (LitV n) = return (pretty n)
  ppr (Add e1 e2) = do
    e1' <- ppr e1
    e2' <- ppr e2
    return $ e1' <+> "+" <+> e2'
  ppr (EVar x) = return (pretty  x)
  ppr (EAnn e t) = do
    e' <- ppr e
    t' <- ppr t
    return $ e' <+>  ":" <+> t'
  ppr (EApp f a) = do
    df <- ppr f
    da <- ppr a
    return $ wrapf f df <+> wraparg a da
  ppr (ELam bnd) =
    lunbind bnd $ \(x, b) -> do
      b' <- ppr b
      return $ "λ" <> pretty x <+>  "→" <+> b'
  ppr (ELamA bnd) =
    lunbind bnd $ \((x, Embed t), b) -> do
      b' <- ppr b
      t' <- ppr t
      return $ "λ(" <> pretty x <+> ":" <+> t' <> ")" <+>  "→" <+> b'
  ppr (ELet bnd) =
    lunbind bnd $ \((x, Embed e1), e2) -> do
      e1' <- ppr e1
      e2' <- ppr e2
      return $ "let" <+> pretty x <+> "=" <+> e1' <+> "in" <+> e2'


instance FPretty Type where
  ppr TUnit = return "()"
  ppr TBool = return "Bool"
  ppr TUnknown = return "?"
  ppr TNum = return "Int"
  ppr (TVar x) = return (pretty x)
  ppr (TEVar (ETS x)) = return ("^" <> pretty x <> "S" )
  ppr (TEVar (ETG x)) = return ("^" <> pretty x <> "G" )
  ppr (TArr a b) = do
    a' <- ppr a
    b' <- ppr b
    return $ Pretty.parens (a' <+> "→" <+> b')
  ppr (TAll b) =
    lunbind b $ \(x, t) -> do
      t' <- ppr t
      return (Pretty.parens $ "∀" <> pretty x <+> Pretty.dot <+> t')


-- deciding whether to add parens to the func of an application
wrapf :: Expr -> FDoc -> FDoc
wrapf f = case f of
  EVar _         -> id
  EApp _ _       -> id

  _             -> Pretty.parens

-- deciding whether to add parens to the arg of an application
wraparg :: Expr -> FDoc -> FDoc
wraparg x = case x of
  EVar _       -> id
  LitV _ -> id
  -- S.BoolV _ -> id
  -- S.StrV _ -> id
  EUnit -> id
  _ -> Pretty.parens
