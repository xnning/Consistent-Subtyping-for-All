{-# LANGUAGE FlexibleContexts #-}
module Language.HigherRank.Typecheck (runInfer) where

import qualified Data.Sequence as S

import           Control.Applicative
import           Control.Monad (unless)
import           Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError, runExcept)
import           Control.Monad.State (MonadState, State, evalState, get, gets, put)
import           Data.Foldable (toList)
import           Data.Maybe (isJust)
import           Data.Monoid ((<>))
import           Data.Sequence (Seq(..))
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

import           Language.HigherRank.Print
import           Language.HigherRank.Types


----------------------
-- | Environment setup
----------------------

data CtxMember
  = CtxVar TyName
  | CtxAssump TmName Type
  | CtxEVar ETVar
  | CtxSolved ETVar Type
  | CtxMarker ETVar
  deriving Show

instance Eq CtxMember where
  CtxVar x == CtxVar y = x == y
  CtxAssump x t == CtxAssump y t' = x == y && aeq t t'
  CtxEVar x == CtxEVar y = x == y
  CtxSolved x t == CtxSolved y t' = x == y && aeq t t'
  CtxMarker x == CtxMarker y = x == y
  _ == _ = False


newtype Ctx = Ctx (Seq CtxMember)
  deriving (Eq, Show, Monoid)

newtype CheckState = CheckState
  { checkCtx :: Ctx
  } deriving (Eq, Show)

defCheckState :: CheckState
defCheckState = CheckState mempty

newtype CheckM a =
  CheckM (FreshMT (ExceptT String (State CheckState)) a)
  deriving ( Functor
           , Applicative
           , Alternative
           , Monad
           , MonadState CheckState
           , MonadError String
           , Fresh
           )

runCheckM :: CheckM a -> Either String a
runCheckM (CheckM x) = evalState (runExceptT (runFreshMT x)) defCheckState


----------------
-- | Misc
----------------



isMono :: Type -> Bool
isMono TUnit = True
isMono TBool = True
isMono TNum = True
isMono (TVar _) = True
isMono (TEVar _) = True
isMono (TArr a b) = isMono a && isMono b
isMono (TAll _) = False
isMono TUnknown = False


(|>) :: Ctx -> CtxMember -> Ctx
(Ctx ctx) |> mem = Ctx (ctx S.|> mem)

ctxElem :: CtxMember -> Ctx -> Bool
ctxElem x (Ctx ctx) = x `elem` ctx

ctxHole :: CtxMember -> Ctx -> Maybe (Ctx, Ctx)
ctxHole mem (Ctx ctx) = if mem `elem` ctx then Just (Ctx a, Ctx (S.drop 1 b)) else Nothing
  where (a, b) = S.breakl (== mem) ctx

ctxHole2 :: CtxMember -> CtxMember -> Ctx -> Maybe (Ctx, Ctx, Ctx)
ctxHole2 mem mem' ctx = do
  (a, ctx') <- ctxHole mem ctx
  (b, c) <- ctxHole mem' ctx'
  return (a, b, c)

ctxAssump :: Ctx -> TmName -> Maybe Type
ctxAssump (Ctx ctx) x = case assumptions of
    [CtxAssump _ t] -> Just t
    [] -> Nothing
    other -> error $ "ctxSolution: internal error — multiple types for variable: " ++ show other
  where isAssump (CtxAssump y _) = x == y
        isAssump _ = False
        assumptions = filter isAssump $ toList ctx

ctxSolution :: Ctx -> ETVar -> Maybe Type
ctxSolution (Ctx ctx) v = case solutions of
    [CtxSolved _ t] -> Just t
    [] -> Nothing
    other -> error $ "ctxSolution: internal error — multiple solutions for variable: " ++ show other
  where isSolution (CtxSolved u _) = v == u
        isSolution _ = False
        solutions = filter isSolution $ toList ctx

ctxUntil :: CtxMember -> Ctx -> Ctx
ctxUntil m (Ctx ctx) = Ctx $ S.takeWhileL (/= m) ctx

typeWF :: (Fresh m, MonadError String m) => Ctx -> Type -> m ()
typeWF _ TUnit = return ()
typeWF _ TBool = return ()
typeWF _ TUnknown = return ()
typeWF _ TNum = return ()
typeWF ctx (TVar v) =
  unless (CtxVar v `ctxElem` ctx) $
  throwError $ "unbound type variable ‘" ++ pprint (TVar v) ++ "’"
typeWF ctx (TEVar v) =
  unless (CtxEVar v `ctxElem` ctx || hasSolution) $
  throwError $ "unbound existential variable ‘" ++ pprint (TEVar v) ++ "’"
  where
    hasSolution = isJust (ctxSolution ctx v)
typeWF ctx (TArr x y) = typeWF ctx x >> typeWF ctx y
typeWF ctx (TAll t) = do
  (x, b) <- unbind t
  typeWF (ctx |> CtxVar x) b


(⊢) :: Ctx -> Type -> Either String ()
ctx ⊢ t = runExcept (runFreshMT (typeWF ctx t))

freeVars :: Type -> [TyName]
freeVars = toListOf fv

applySubst :: Fresh m => Ctx -> Type -> m Type
applySubst _ TUnit = return TUnit
applySubst _ TBool = return TBool
applySubst _ TUnknown = return TUnknown
applySubst _ TNum = return TNum
applySubst _ t@(TVar _) = return t
applySubst ctx t@(TEVar v) = maybe (return t) (applySubst ctx) (ctxSolution ctx v)
applySubst ctx (TArr a b) = TArr <$> applySubst ctx a <*> applySubst ctx b
applySubst ctx (TAll t) = do
  (x, b) <- unbind t
  b' <- applySubst ctx b
  return $ TAll (bind x b')


getCtx :: CheckM Ctx
getCtx = gets checkCtx

putCtx :: Ctx -> CheckM ()
putCtx ctx = get >>= \s -> put s { checkCtx = ctx }

modifyCtx :: (Ctx -> Ctx) -> CheckM ()
modifyCtx f = putCtx . f =<< getCtx

freshEVar :: CheckM TyName
freshEVar = fresh (s2n "α")

checkTypeWF :: Type -> CheckM ()
checkTypeWF t = getCtx >>= \ctx -> typeWF ctx t

--------------------------------
-- | Consistent Subtyping
--------------------------------


tySub :: Type -> Type -> CheckM ()
tySub TUnit TUnit = return ()
tySub TNum TNum = return ()
tySub (TVar a) (TVar b) | a == b = return ()
tySub (TEVar (ETS a)) (TEVar (ETS b)) | a == b = return ()
tySub (TEVar (ETG a)) (TEVar (ETG b)) | a == b = return ()
tySub t TUnknown = do
  ctx <- getCtx
  ctx' <- contaminate t ctx
  putCtx ctx'
tySub TUnknown t = do
  ctx <- getCtx
  ctx' <- contaminate t ctx
  putCtx ctx'
tySub (TArr a b) (TArr a' b') = do
  tySub a' a
  ctx <- getCtx
  sb <- applySubst ctx b
  sb' <- applySubst ctx b'
  tySub sb sb'
tySub (TAll t) b = do
  (a, body) <- unbind t
  as <- ETS <$> freshEVar
  modifyCtx (\c -> c |> CtxMarker as |> CtxEVar as)
  tySub (subst a (TEVar as) body) b
  modifyCtx (ctxUntil (CtxMarker as))
tySub a (TAll t) = do
  (b, body) <- unbind t
  modifyCtx (\c -> c |> CtxVar b)
  tySub a body
  modifyCtx (ctxUntil (CtxVar b))
-- Jeremy: Should I check if â exists in the context?
tySub (TEVar â) (TEVar â') = instL â (TEVar â') <|> instR (TEVar â) â'
tySub (TEVar â) a | extract â `notElem` freeVars a = instL â a
tySub a (TEVar â) | extract â `notElem` freeVars a = instR a â
tySub a b = throwError $ "type mismatch: expected " ++ pprint b ++ ", given " ++ pprint a


extract :: ETVar -> TyName
extract (ETS n) = n
extract (ETG n) = n

contaminate :: Type -> Ctx -> CheckM Ctx
contaminate _ ctx@(Ctx Empty) = return ctx
contaminate t (Ctx (ctx :|> CtxEVar (ETS as)))
  | as `elem` freeVars t = do
      ag <- ETG <$> freshEVar
      ctx' <- contaminate t (Ctx ctx)
      return $ ctx' |> CtxEVar ag |> CtxSolved (ETS as) (TEVar ag)
  | otherwise = do
      ctx' <- contaminate t (Ctx ctx)
      return $ ctx' |> CtxEVar (ETS as)
contaminate t (Ctx (ctx :|> a)) = do
      ctx' <- contaminate t (Ctx ctx)
      return $ ctx' |> a

--------------------------------
-- | Instantiation
--------------------------------


instL :: ETVar -> Type -> CheckM ()
instL â t = getCtx >>= go
  -- Defer to a helper function so we can pattern match/guard against the
  -- current context.
  where
    go ctx -- ^InstLSolveS & instLSolveG
      | True <- isMono t
      , Just (l, r) <- ctxHole (CtxEVar â) ctx
      , Right _ <- l ⊢ t = putCtx $ l |> CtxSolved â t <> r
    go _ -- ^InstLSolveUG
      | False <- isETS â
      , TUnknown <- t = return ()
    go ctx -- ^InstLSolveUS
      | True <- isETS â
      , TUnknown <- t
      , Just (l, r) <- ctxHole (CtxEVar â) ctx = do
        ag <- ETG <$> freshEVar
        putCtx $ l |> CtxEVar ag |> CtxSolved â (TEVar ag) <> r
    go ctx -- ^InstLReachSG1
      | TEVar (ETG â') <- t
      , True <- isETS â
      , Just (l, m, r) <- ctxHole2 (CtxEVar â) (CtxEVar (ETG â')) ctx = do
          ag <- ETG <$> freshEVar
          putCtx $ l |> CtxEVar ag |> CtxSolved â (TEVar ag) <> m |> CtxSolved (ETG â') (TEVar ag) <> r
    go ctx -- ^InstLReachSG2
      | TEVar (ETS â') <- t
      , False <- isETS â
      , Just (l, m, r) <- ctxHole2 (CtxEVar â) (CtxEVar (ETG â')) ctx = do
          bg <- ETG <$> freshEVar
          putCtx $ l |> CtxEVar bg |> CtxSolved (ETS â') (TEVar bg) <> m |> CtxSolved â (TEVar bg) <> r
    go ctx -- ^InstLReachOther
      | TEVar â' <- t
      , Just (l, m, r) <- ctxHole2 (CtxEVar â) (CtxEVar â') ctx =
          putCtx $ l |> CtxEVar â  <> m |> CtxSolved â' (TEVar â) <> r
    go ctx -- ^InstLArr
      | Just (l, r) <- ctxHole (CtxEVar â) ctx
      , TArr a b <- t = do
        â1 <- (if isETS â then ETS else ETG) <$> freshEVar
        â2 <- (if isETS â then ETS else ETG) <$> freshEVar
        putCtx $ l |> CtxEVar â2 |> CtxEVar â1 |> CtxSolved â (TArr (TEVar â1) (TEVar â2)) <> r
        instR a â1
        ctx' <- getCtx
        b' <- applySubst ctx' b
        instL â2 b'
    go ctx -- ^InstLAllR
      | TAll s <- t = do
        (a, body) <- unbind s
        putCtx $ ctx |> CtxVar a
        instL â body
        modifyCtx $ ctxUntil (CtxVar a)
        -- Just (ctx', _) <- ctxHole (CtxVar a) <$> getCtx
        -- putCtx ctx'
    go _ = throwError $ "instL: failed to instantiate " ++ pprint (TEVar â) ++ " to " ++ pprint t

instR :: Type -> ETVar -> CheckM ()
instR t â = getCtx >>= go
  -- Defer to a helper function so we can pattern match/guard against the
  -- current context.
  where
    go ctx -- ^ InstRSolveS & InstRSolveG
      | True <- isMono t
      , Just (l, r) <- ctxHole (CtxEVar â) ctx
      , Right _ <- l ⊢ t = putCtx $ l |> CtxSolved â t <> r
    go _ -- ^InstLSolveUG
      | False <- isETS â
      , TUnknown <- t = return ()
    go ctx -- ^InstLSolveUS
      | True <- isETS â
      , TUnknown <- t
      , Just (l, r) <- ctxHole (CtxEVar â) ctx = do
        ag <- ETG <$> freshEVar
        putCtx $ l |> CtxEVar ag |> CtxSolved â (TEVar ag) <> r
    go ctx -- ^InstLReachSG1
      | TEVar (ETG â') <- t
      , True <- isETS â
      , Just (l, m, r) <- ctxHole2 (CtxEVar â) (CtxEVar (ETG â')) ctx = do
          ag <- ETG <$> freshEVar
          putCtx $ l |> CtxEVar ag |> CtxSolved â (TEVar ag) <> m |> CtxSolved (ETG â') (TEVar ag) <> r
    go ctx -- ^InstLReachSG2
      | TEVar (ETS â') <- t
      , False <- isETS â
      , Just (l, m, r) <- ctxHole2 (CtxEVar â) (CtxEVar (ETG â')) ctx = do
          bg <- ETG <$> freshEVar
          putCtx $ l |> CtxEVar bg |> CtxSolved (ETS â') (TEVar bg) <> m |> CtxSolved â (TEVar bg) <> r
    go ctx -- ^InstLReachOther
      | TEVar â' <- t
      , Just (l, m, r) <- ctxHole2 (CtxEVar â) (CtxEVar â') ctx =
          putCtx $ l |> CtxEVar â <> m |> CtxSolved â' (TEVar â) <> r
    go ctx -- ^InstRArr
      | TArr a b <- t
      , Just (l, r) <- ctxHole (CtxEVar â) ctx = do
        â1 <- (if isETS â then ETS else ETG) <$> freshEVar
        â2 <- (if isETS â then ETS else ETG) <$> freshEVar
        putCtx $ l |> CtxEVar â2 |> CtxEVar â1 |> CtxSolved â (TArr (TEVar â1) (TEVar â2)) <> r
        instL â1 a
        ctx' <- getCtx
        b' <- applySubst ctx' b
        instR b' â2
    go ctx -- ^InstRAllLL
      | TAll s <- t = do
        (a, body) <- unbind s
        â' <- ETS <$> freshEVar
        putCtx $ ctx |> CtxMarker â' |> CtxEVar â'
        instR (subst a (TEVar â') body) â
        modifyCtx $ ctxUntil (CtxMarker â')
        -- Just (ctx', _) <- ctxHole (CtxMarker â') <$> getCtx
        -- putCtx ctx'
    go _ = throwError $ "instR: failed to instantiate " ++ pprint (TEVar â) ++ " to " ++ pprint t

--------------------------------
-- | Checking
--------------------------------

check :: Expr -> Type -> CheckM ()
check EUnit TUnit = return ()
check (LitV _) TNum = return ()
check e (TAll t) = do
  (a, body) <- unbind t
  modifyCtx (\c -> c |> CtxVar a)
  check e body
  modifyCtx (ctxUntil (CtxVar a))
check (ELam e) (TArr a b) = do
  (x, body) <- unbind e
  modifyCtx (\c -> c |> CtxAssump x a)
  check body b
  modifyCtx (ctxUntil (CtxAssump x a))
check (ELet b) t = do
  ((x, Embed e1), e2) <- unbind b
  t1 <- infer e1
  modifyCtx (\c -> c |> CtxAssump x t1)
  check e2 t
  modifyCtx (ctxUntil (CtxAssump x t1))
check e b = do
  a <- infer e
  ctx <- getCtx
  a' <- applySubst ctx a
  b' <- applySubst ctx b
  tySub a' b'

--------------------------------
-- | Inference
--------------------------------

infer :: Expr -> CheckM Type
infer EUnit = return TUnit
infer (LitV _) = return TNum
infer (Add e1 e2) = do
  check e1 TNum
  check e2 TNum
  return TNum
infer (EVar x) = do
  ctx <- getCtx
  maybe (throwError $ "unbound variable " ++ pprint (EVar x)) return (ctxAssump ctx x)
infer (EAnn e a) = checkTypeWF a >> check e a >> return a
infer (ELam e) = do
  (x, body) <- unbind e
  â <- ETS <$> freshEVar
  â' <- ETS <$> freshEVar
  modifyCtx (\c -> c |> CtxEVar â |> CtxEVar â' |> CtxAssump x (TEVar â))
  check body (TEVar â')
  modifyCtx (ctxUntil (CtxAssump x (TEVar â)))
  return $ TArr (TEVar â) (TEVar â')
infer (ELamA e) = do
  ((x, Embed t), body) <- unbind e
  checkTypeWF t
  â <- ETS <$> freshEVar
  modifyCtx (\c -> c |> CtxEVar â |> CtxAssump x t)
  check body (TEVar â)
  modifyCtx (ctxUntil (CtxAssump x t))
  return $ TArr t (TEVar â)
infer (EApp e1 e2) = do
  a <- infer e1
  ctx <- getCtx
  a' <- applySubst ctx a
  (a1, a2) <- matching a'
  ctx' <- getCtx
  a1' <- applySubst ctx' a1
  check e2 a1'
  return a2
infer (ELet b) = do
  ((x, Embed e1), e2) <- unbind b
  t <- infer e1
  â <- ETS <$> freshEVar
  modifyCtx (\c -> c |> CtxEVar â |> CtxAssump x t)
  check e2 (TEVar â)
  modifyCtx (ctxUntil (CtxAssump x t))
  return $ TEVar â
infer ETrue = return TBool
infer EFalse = return TBool


matching :: Type -> CheckM (Type, Type)
matching TUnknown  = return (TUnknown, TUnknown)
matching (TEVar â) = do
  â1 <- (if isETS â then ETS else ETG) <$> freshEVar
  â2 <- (if isETS â then ETS else ETG) <$> freshEVar
  Just (l, r) <- ctxHole (CtxEVar â) <$> getCtx
  putCtx $ l |> CtxEVar â2 |> CtxEVar â1 |> CtxSolved â (TArr (TEVar â1) (TEVar â2)) <> r
  return (TEVar â1, TEVar â2)
matching (TAll t) = do
  (a, body) <- unbind t
  â <- ETS <$> freshEVar
  modifyCtx (\c -> c |> CtxEVar â)
  matching (subst a (TEVar â) body)
matching (TArr a b) = return (a, b)
matching t = throwError $ "cannot matching " ++ pprint t


runInfer :: Expr -> Either String Type
runInfer = runCheckM . wrap
  where
    wrap :: Expr -> CheckM Type
    wrap e = do
      t <- infer e
      ctx <- getCtx
      applySubst ctx t
