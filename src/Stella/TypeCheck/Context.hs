module Stella.TypeCheck.Context where

import Stella.Abs

-- Контекст типов ошибок
data ExceptionContext
    = ExnTypeNotDeclared
    | ExnTypeDecl Type
    | ExnOpenVariant [VariantFieldType]
  deriving (Show, Eq)

-- Окружение
data Env = Env
    { envVars :: [(StellaIdent, Type)] -- имя переменной -> её тип
    , envExn  :: ExceptionContext      -- контекст типов ошибок
    , isAmbTyAsBot :: Bool             -- поддержано ли разрешение неоднозначных типов за счет TypeBottom
    , isSubtyping :: Bool              -- поддержана ли подтипизация
    , isReconstruction :: Bool         -- поддержана ли реконструкция типов
    }
    deriving (Show, Eq)