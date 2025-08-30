# Stella Typechecker — Этап 1

## 1. Кратко о проекте

На данном этапе проекта необходимо реализовать программу для **проверки типов** исходного кода на упрощённом функциональном фрагменте языка **Stella1**.

**Моя реализация содержит следующие конструкции и расширения:**

1. Ядро языка Stella: логические типы, натуральные числа, функции.
2. Для расширения `#unit-type`: `TypeUnit`, `ConstUnit`.
3. Для расширений `#pairs` и `#tuples`: `TypeTuple`, `Tuple`, `DotTuple`.
4. Для расширения `#records`: `TypeRecord`, `Record`, `DotRecord`.
5. Для расширения `#let-bindings`: `Let`, `APatternBinding`, `PatternVar`.
6. Для расширения `#type-ascriptions`: `TypeAsc`.
7. Для расширения `#sum-types`: `TypeSum`, `Inl`, `Inr`, `Match`, `AMatchCase`, `PatternInl`, `PatternInr`, `PatternVar`.
8. Для расширения `#lists`: `TypeList`, `List`, `ConsList`, `Head`, `Tail`, `IsEmpty`.
9. Для расширения `#variants`: `TypeVariant`, `AVariantFieldType`, `SomeTyping`, `Variant`, `SomeExprData`, `PatternVariant`, `SomePatternData`.
10. Для расширения `#fixpoint-combinator`: `Fix`.

**Также реализованы все необязательные расширения:**

1. `#natural-literals`: `ConstInt`.
2. `#nested-function-declarations`: `DeclFun`.
3. `#nullary-functions` и `#multiparameter-functions`.
4. `#structural-patterns`: расширенные и вложенные образцы в `let`-связываниях и `match`-выражениях.
5. `#nullary-variant-labels`: теги без данных в вариантах.
6. `#letrec-bindings` с `#pattern-ascriptions`: `LetRec`, а также `PatternAsc` для указания типа рекурсивно определяемой переменной.

---

## 2. Рекомендуемая версия компилятора

Проект рассчитан на **GHC** версии:

```
The Glorious Glasgow Haskell Compilation System, version 9.4.8
```

---

## 3. Структура проекта

Примерная структура репозитория:

```
stella-typechecker/
├─ src/               # исходный код тайпчекера
│  └─ Stella/
│      └─ TypeCheck.hs
├─ examples/          # тестовые программы
│  ├─ core_basics/
│  ├─ list_succ/
│  ├─ patterns_succ/
│  └─ ...
├─ Stella.cf          # грамматика для BNFC
├─ Makefile           # сборка и запуск тестов
└─ README.md          # данный файл
```

---

## 4. Сборка и запуск

### Генерация парсера

```bash
make bnfc
```

### Сборка тайпчекера

```bash
make all
```

### Очистка проекта

```bash
make clean       # только скомпилированные файлы
make distclean   # удаляет всю директорию src
```

### Запуск тестов

```bash
make tests
```

Или вручную:

```bash
cd examples
./check_all.sh
```
