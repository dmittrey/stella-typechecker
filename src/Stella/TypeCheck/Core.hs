module Stella.TypeCheck.Core where

import Stella.TypeCheck.Error
import Stella.TypeCheck.Context
import Stella.TypeCheck.Subsumption
import Stella.TypeCheck.CheckInfer
import Stella.TypeCheck.Unification

import Stella.Abs

-- Core, #nested-function-declarations, #nullary-functions
declCheck :: Env -> Decl -> (CheckResult, Env)
declCheck env (DeclFun anns funIdent@(StellaIdent funName) paramsAnn retTy throwTy decls expr) =
    let
        -- вычисляем тип возвращаемого значения
        resultTy = case retTy of
                      NoReturnType      -> TypeUnit
                      SomeReturnType ty -> ty

        -- тип самой функции
        funTy    = TypeFun [t | AParamDecl _ t <- paramsAnn] resultTy

        -- функция должна быть доступна самой себе для рекурсии
        envWithFun = env { envVars = (funIdent, funTy) : envVars env }

        -- добавляем параметры в локальное окружение (новый слой)
        env' = envWithFun { envVars = [(pIdent, t) | AParamDecl pIdent t <- paramsAnn] ++ envVars envWithFun }

        -- сначала проверяем внутренние функции/decls
        (resInner, envInner) = foldl step (CheckOk emptyUEqs, env') decls

        -- проверка тела функции
        resBody = exprCheck envInner expr resultTy

        -- проверка основной функции main (правильная арность)
        isMainUnary =
            if funName == "main"
                then if length paramsAnn /= 1
                       then CheckErr ERROR_INCORRECT_ARITY_OF_MAIN
                       else CheckOk emptyUEqs
                else CheckOk emptyUEqs

        -- объединяем все результаты в одно UEqs
        combined :: CheckResult
        combined = do
            c1 <- isMainUnary
            c2 <- resBody
            c3 <- resInner
            return (c1 <> c2 <> c3)

    in (combined, envWithFun)
  where
    step :: (CheckResult, Env) -> Decl -> (CheckResult, Env)
    step (CheckOk c, envAcc) d = declCheck envAcc d
    step (CheckErr err, envAcc) _ = (CheckErr err, envAcc)

declCheck e (DeclExceptionType _) = (CheckOk emptyUEqs, e)
declCheck e (DeclExceptionVariant _ _) = (CheckOk emptyUEqs, e)

declCheck e d = (CheckErr (ERROR_DECL_CHECK_NOT_IMPLEMENTED d), e)