module LICK.Eval

import Data.List

import LICK.Expr
import LICK.ProgramType

%default total


||| Convert a ProgramType to an Idris equivalent.
public export
ProgramTypeToType
   : ProgramType
  -> Type

ProgramTypeToType (PFunction x y)
   = ProgramTypeToType x
  -> ProgramTypeToType y

ProgramTypeToType PInt
  = Int


||| Convert a Context to a nested tuple HList of Idris-equivalent
||| types. Like an unindexed HVect.
public export
ContextToHList
   : Context
  -> Type
ContextToHList []
  = ()

ContextToHList (x :: xs)
  = ( ProgramTypeToType x
    , ContextToHList xs
    )


||| Retrieve a value from the currently working program context.
export
get
   : Elem programType context
  -> ContextToHList context
  -> ProgramTypeToType programType

get Here (value, _)
  = value

get (There later) (_, value)
  = get later value


||| Evaluate a program within a given context.
export
eval
   : {context : Context}
  -> ContextToHList context
  -> Expr context programType
  -> ProgramTypeToType programType
eval context (Var reference)
  = get reference context
eval context (Abs parameter body)
  = \x => eval (x, context) body
eval context (App function argument)
  = eval context function (eval context argument)


-- Tests


Apply2
  : Expr context
      (PFunction
        (PFunction a a)
        (PFunction a a))
Apply2 {a}
  = Abs (PFunction a a)
        (Abs a (App (Var (There Here))
                    (Var Here)))

Eg0
  : eval {context = []} ()
         (Apply2 {a = PInt})
         (+ 1) 5
  = 6

Eg0
  = Refl


Eg1
  : eval {context = [PInt, PFunction PInt PInt]} (3, ((+1), ()))
         (App (Var (There Here)) (Var Here))
  = 4

Eg1
  = Refl

