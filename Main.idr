module Main


import Data.List


%default total

data ProgramType
  = PFunction ProgramType ProgramType
  | PUnit

domainMismatch : (i = i' -> Void) -> (PFunction i o = PFunction i' o') -> Void
domainMismatch f Refl = f Refl

codomainMismatch : (o = o' -> Void) -> (PFunction i o = PFunction i' o') -> Void
codomainMismatch f Refl = f Refl

funNotUnit : PFunction i o = PUnit -> Void
funNotUnit Refl impossible

implementation DecEq ProgramType where
  decEq (PFunction i o) (PFunction i' o')
    with (decEq i i', decEq o o')
      decEq (PFunction i o) (PFunction i o) | (Yes Refl, Yes Refl) = Yes Refl
      decEq (PFunction i o) (PFunction i' o') | (No a, b) = No (domainMismatch a)
      decEq (PFunction i o) (PFunction i' o') | (a, No b) = No (codomainMismatch b)
  decEq (PFunction i o) PUnit = No funNotUnit
  decEq PUnit (PFunction x y) = No (funNotUnit . sym)
  decEq PUnit PUnit = Yes Refl

Context : Type
Context = List ProgramType


data Expr : (context : Context) -> ProgramType -> Type where

  Var
     : (reference : Elem programType context)
    -> Expr context programType

  Abs
     : (parameter : ProgramType)
    -> (body      : Expr (parameter :: context) programType)
    -> Expr context (PFunction parameter programType)

  App
     : (function : Expr context (PFunction parameter return))
    -> (argument : Expr context parameter)
    -> Expr context return

hereNotThere : Not (Here = There later)
hereNotThere Refl impossible

wasn'tThere : Not (l = r) -> Not (There l = There r)
wasn'tThere f Refl = f Refl

decEqElem : (l, r : Elem x xs) -> Dec (l = r)
decEqElem Here Here = Yes Refl
decEqElem Here (There later) = No hereNotThere
decEqElem (There later) Here = No (hereNotThere . sym)
decEqElem (There l) (There r) with (decEqElem l r)
  decEqElem (There r) (There r) | (Yes Refl) = Yes Refl
  decEqElem (There l) (There r) | (No contra) = No (wasn'tThere contra)

shrinkContext : (idx : Elem y xs) -> Elem x xs -> Not (x = y) -> Elem x (dropElem xs idx)
shrinkContext Here Here y = absurd (y Refl)
shrinkContext Here (There later) y = later
shrinkContext (There later) Here y = Here
shrinkContext (There later) (There x) y = There (shrinkContext later x y)

shrink2 : (l, r : Elem x xs) -> Not (l = r) -> Elem x (dropElem xs r)
shrink2 Here Here x = absurd (x Refl)
shrink2 Here (There later) x = Here
shrink2 (There later) Here x = later
shrink2 (There later) (There y) x = There (shrink2 later y (x . cong))

baitAndSwitch : Elem x (dropElem (p :: xs) (There idx)) -> Elem x (p :: dropElem xs idx)
baitAndSwitch Here = Here
baitAndSwitch (There later) = There later

help : Expr (a :: b :: c) t -> Expr (b :: a :: c) t
help (Var Here) = Var (There Here)
help (Var (There Here)) = Var Here
help (Var (There (There x))) = Var (There (There x))
help (Abs parameter body) = Abs parameter ?what
help (App function argument) = ?help_rhs_3

expandContext : Expr context programType -> Expr (p :: context) programType
expandContext (Var reference) = Var (There reference)
expandContext (Abs parameter body) = Abs parameter (help (expandContext body))
expandContext (App function argument) = App (expandContext function) (expandContext argument)

{-
substitute : (reference : Elem argType context) -> (body : Expr context programType) -> (argument : Expr (dropElem context reference) argType) -> Expr (dropElem context reference) programType
substitute {argType} {programType} reference (Var x) argument with (decEq programType argType)
  substitute {argType = programType} {programType = programType} reference (Var x) argument | (Yes Refl)  with (decEqElem x reference)
    substitute {argType = programType} {programType = programType} x (Var x) argument | (Yes Refl)  | (Yes Refl) = argument
    substitute {argType = programType} {programType = programType} reference (Var x) argument | (Yes Refl)  | (No contra) = Var (shrink2 x reference contra)
  substitute {argType = argType} {programType = programType} reference (Var x) argument     | (No contra) = Var (shrinkContext reference x contra)
substitute reference (Abs parameter body) argument
  = Abs parameter (substitute ?aoeu ?body (?test))
  -- = Abs parameter (?hahsubstitute (?there reference) body argument)
substitute reference (App function x) argument
  = App (substitute reference function argument)
        (substitute reference x        argument)
        -}

{-
reduce : Expr context programType -> Expr context programType
reduce (Abs parameter body)
  = Abs parameter (reduce body)
reduce (App function argument)
  with (reduce function, reduce argument)
    | (Abs parameter body, argument')
        = reduce (substitute Here body argument')
    | (function', argument')
        = App function' argument'
reduce irreducible
  = irreducible
-}

ProgramTypeToType : ProgramType -> Type
ProgramTypeToType (PFunction x y)
  = ProgramTypeToType x -> ProgramTypeToType y
ProgramTypeToType PUnit
  = ()

ContextToHList : Context -> Type
ContextToHList [] = ()
ContextToHList (x :: xs)
  = (ProgramTypeToType x, ContextToHList xs)

VariableToType : (context : Context) -> Elem x context -> Type
VariableToType (x :: xs) elem with (elem)
  | Here          = ProgramTypeToType x
  | (There later) = VariableToType xs later

get : (context : Context) -> (index : Elem x context) -> VariableToType context index
get (head :: _) Here = ProgramTypeToType head
get (_ :: tail) (There later) = get tail later

eval
   : {context : Context}
  -> ContextToHList context
  -> Expr context programType
  -> ProgramTypeToType programType
eval context (Var reference)
  = get context reference
eval context (Abs parameter body)
  = \x => eval (x, context) body
eval context (App function argument)
  = eval context function (eval context argument)



-- Examples

eg0 : Expr context (PFunction PUnit PUnit)
eg0 = Abs PUnit (Var Here)

eg1 : Expr context (PFunction PUnit PUnit)
eg1 = Abs PUnit (App eg0 (Var Here))

id : Expr context (PFunction a a)
id {a} = Abs a (Var Here)

const : Expr context (PFunction a (PFunction b a))
const {a} {b} = Abs a (Abs b (Var (There Here)))

