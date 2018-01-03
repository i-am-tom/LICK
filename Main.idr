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

varHelp : (bound : Context) -> Elem t (bound ++ free) -> Elem t (bound ++ a :: free)
varHelp [] Here = There Here
varHelp [] (There later) = There (There later)
varHelp (x :: xs) Here = Here
varHelp (x :: xs) (There later) = There (varHelp xs later)

help : (bound : Context) -> Expr (bound ++ c) t -> Expr (bound ++ a :: c) t
help bound (Var exs) = Var (varHelp bound exs)
help bound (Abs parameter body) = Abs parameter (help (parameter :: bound) body)
help bound (App function argument) = App (help bound function) (help bound argument)

ndSwitch : Expr (dropElem (p :: xs) (There idx)) t -> Expr (p :: dropElem xs idx) t
ndSwitch (Var reference) = Var (baitAndSwitch reference)
ndSwitch (Abs parameter body) = Abs parameter body
ndSwitch (App function argument) = App (ndSwitch function) (ndSwitch argument)

switchNd : Expr (p :: dropElem xs idx) t -> Expr (dropElem (p :: xs) (There idx)) t
switchNd (Var reference) = Var reference
switchNd (Abs parameter body) = Abs parameter body
switchNd (App function argument) = App (switchNd function) (switchNd argument)

substitute : (reference : Elem argType context) -> (body : Expr context programType) -> (argument : Expr (dropElem context reference) argType) -> Expr (dropElem context reference) programType
substitute {argType} {programType} reference (Var x) argument with (decEq programType argType)
  substitute {argType = programType} {programType = programType} reference (Var x) argument | (Yes Refl)  with (decEqElem x reference)
    substitute {argType = programType} {programType = programType} x (Var x) argument | (Yes Refl)  | (Yes Refl) = argument
    substitute {argType = programType} {programType = programType} reference (Var x) argument | (Yes Refl)  | (No contra) = Var (shrink2 x reference contra)
  substitute {argType = argType} {programType = programType} reference (Var x) argument     | (No contra) = Var (shrinkContext reference x contra)
substitute reference (Abs parameter body) argument
  = Abs parameter (ndSwitch (substitute (There reference) body (switchNd (help [] argument))))
substitute reference (App function x) argument
  = App (substitute reference function argument)
        (substitute reference x        argument)

reduceApp : Expr context (PFunction i o) -> Expr context i -> Expr context o
reduceApp (Var reference) y = App (Var reference) y
reduceApp (App function argument) y = App (App function argument) y
reduceApp (Abs parameter body) argument = substitute Here body argument

reduce : Expr context programType -> Expr context programType
reduce (Abs parameter body)
  = Abs parameter (reduce body)
reduce (App function argument)
  with (reduce function, reduce argument)
    | (function', argument')
        = reduceApp function' argument'
reduce (Var x)
  = Var x

ProgramTypeToType : ProgramType -> Type
ProgramTypeToType (PFunction x y)
  = ProgramTypeToType x -> ProgramTypeToType y
ProgramTypeToType PUnit
  = ()

ContextToHList : Context -> Type
ContextToHList [] = ()
ContextToHList (x :: xs)
  = (ProgramTypeToType x, ContextToHList xs)

ContextReferenceToType : (context : Context) -> (index : Elem x context) -> Type
ContextReferenceToType (head :: _) Here = ProgramTypeToType head
ContextReferenceToType (_ :: tail) (There later) = ContextReferenceToType tail later

lookupVar : Elem t xs -> ContextToHList xs -> ProgramTypeToType t
lookupVar Here (a, b) = a
lookupVar (There later) (a, b) = lookupVar later b

eval
   : {context : Context}
  -> ContextToHList context
  -> Expr context programType
  -> ProgramTypeToType programType
eval context (Var reference)
  = lookupVar reference context
eval context (Abs parameter body)
  = \x => eval (x, context) body
eval context (App function argument)
  = eval context function (eval context argument)



-- Examples

Eg0 : Expr context (PFunction PUnit PUnit)
Eg0 = Abs PUnit (Var Here)

Eg1 : Expr context (PFunction PUnit PUnit)
Eg1 = Abs PUnit (App Eg0 (Var Here))

id : Expr context (PFunction a a)
id {a} = Abs a (Var Here)

const : Expr context (PFunction a (PFunction b a))
const {a} {b} = Abs a (Abs b (Var (There Here)))

prf : reduce (Eg1 {context = []}) = Eg0 {context = []}
prf = Refl

prf2 : eval {context = []} () Eg1 = eval {context = []} () Eg0
prf2 = Refl

