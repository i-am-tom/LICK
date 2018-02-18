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
  -> Expression context programType
  -> ProgramTypeToType programType
eval context (Variable reference)
  = get reference context
eval context (Abstraction parameter body)
  = \x => eval (x, context) body
eval context (Application function argument)
  = eval context function (eval context argument)


-- Tests


Apply2
  : Expression context
      (PFunction
        (PFunction a a)
        (PFunction a a))
Apply2 {a}
  = Abstraction
      (PFunction a a)
      (Abstraction a (Application (Variable (There Here))
                                  (Variable Here)))

Eg0
  : eval {context = []} ()
         (Apply2 {a = PInt})
         (+ 1) 5
  = 6

Eg0
  = Refl


Eg1
  : eval {context = [PInt, PFunction PInt PInt]} (3, ((+1), ()))
         (Application (Variable (There Here)) (Variable Here))
  = 4

Eg1
  = Refl

