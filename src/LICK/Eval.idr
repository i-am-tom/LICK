module LICK.Eval

import Data.HVect
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
ContextTypes
   : (context : Context)
  -> Vect (length context) Type

ContextTypes []
  = []

ContextTypes (x :: xs)
   = ProgramTypeToType x
  :: ContextTypes xs


||| Retrieve a value from the currently working program context.
get
   : Elem programType context
  -> HVect (ContextTypes context)
  -> ProgramTypeToType programType

get Here (head :: _)
  = head

get (There later) (_ :: tail)
  = get later tail


||| Evaluate a program within a given context.
export
eval
   : {context : Context}
  -> HVect (ContextTypes context)
  -> Expression context programType
  -> ProgramTypeToType programType
eval context (Variable reference)
  = get reference context
eval context (Abstraction parameter body)
  = \x => eval (x :: context) body
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
  : eval {context = []} []
         (Apply2 {a = PInt})
         (+ 1) 5
  = 6

Eg0
  = Refl


Eg1
  : eval {context = [PInt, PFunction PInt PInt]} [3, (+1)]
         (Application (Variable (There Here)) (Variable Here))
  = 4

Eg1
  = Refl
