module Stella.TypeInfer where

import Stella.TypeCheck

import Stella.Abs
import Stella.ErrM

data InferResult = InferOk Type | InferErr CErrType
  deriving (Show, Eq)

declInfer :: Env -> Decl -> Err (StellaIdent, Type)
-- T-Abs
declInfer env (DeclFun _ name params _ _ _ body) =
    let paramEnv       = [(ident, t) | AParamDecl ident t <- params]
        envWithParams  = paramEnv ++ env
    in case exprInfer envWithParams body of
        InferOk tfunc -> Ok (name, TypeFun [t | AParamDecl _ t <- params] tfunc)
        InferErr err -> Bad $ show err

declInfer _ (DeclFunGeneric _ _ _ _ _ _ _ _) =
    Bad "DeclFunGeneric not supported"
declInfer _ (DeclTypeAlias _ _) =
    Bad "DeclTypeAlias not supported"
declInfer _ (DeclExceptionType _) =
    Bad "DeclExceptionType not supported"
declInfer _ (DeclExceptionVariant _ _) =
    Bad "DeclExceptionVariant not supported"

exprInfer :: Env -> Expr -> InferResult
-- T-Abs
exprInfer env (Abstraction params e) =
    let paramEnv       = [(ident, t) | AParamDecl ident t <- params]
        envWithParams  = paramEnv ++ env
    in case exprInfer envWithParams e of
        InferOk ty -> InferOk (TypeFun [t | AParamDecl _ t <- params] ty)
        InferErr err -> InferErr err

-- T-True
exprInfer _ ConstTrue  = InferOk TypeBool
-- T-False
exprInfer _ ConstFalse = InferOk TypeBool
-- T-If
exprInfer env (If e1 e2 e3) =
    let
        t1 = exprInfer env e1
        t2 = exprInfer env e2
        t3 = exprInfer env e3
    in case t1 of
        InferOk TypeBool ->
            case (t2, t3) of 
                (InferOk ty2, InferOk ty3) ->
                    if ty2 == ty3
                    then InferOk ty2
                    else InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e3 ty2 ty3)
                (InferErr err2, _) ->
                    InferErr err2
                (_, InferErr err3) ->
                    InferErr err3
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e1 TypeBool ty)

        InferErr err -> InferErr err

-- T-Zero
exprInfer _ (ConstInt 0) = InferOk TypeNat
-- T-Succ
exprInfer env (Succ e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeNat
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)

        InferErr err -> InferErr err
-- T-Pred
exprInfer env (Pred e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeNat
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)

        InferErr err -> InferErr err
-- T-IsZero
exprInfer env (IsZero e) = do
    case exprInfer env e of
        InferOk TypeNat -> InferOk TypeBool
        InferOk ty -> InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e TypeNat ty)

        InferErr err -> InferErr err
-- T-NatRec
exprInfer env (NatRec e1 e2 e3) =
    let
        t1 = exprInfer env e1
        t2 = exprInfer env e2
        t3 = exprInfer env e3
    in case t1 of
        InferOk TypeNat ->
            case t2 of 
                InferOk ty2 ->
                    case t3 of
                        InferOk (TypeFun [TypeNat] (TypeFun [ty21] ty22)) ->
                            if (ty2 == ty21 && ty2 == ty22)
                            then InferOk ty2
                            else InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e3 (TypeFun [TypeNat] (TypeFun [ty2] ty2)) (TypeFun [TypeNat] (TypeFun [ty21] ty22)))
                        InferErr err -> InferErr err
                InferErr err -> InferErr err
        InferOk ty ->
            InferErr (ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION e1 TypeNat ty)

        InferErr err -> InferErr err

-- T-Var
exprInfer env (Var ident) =
    case lookup ident env of
        Just t  -> InferOk t
        Nothing -> InferErr (ERROR_UNDEFINED_VARIABLE ident)

-- T-App
exprInfer env (Application e1 e2list) =
    case exprInfer env e1 of
        InferOk (TypeFun tys retTy) ->
            case (exprListCheck env e2list tys) of
                CheckOk -> InferOk retTy
                CheckErr err -> InferErr err
        InferOk _ -> InferErr ERROR_NOT_A_FUNCTION

        InferErr err -> InferErr err

-- Other
exprInfer _ e = InferErr (I_ERROR_EXPR_NOT_IMPLEMENTED_YET e)
