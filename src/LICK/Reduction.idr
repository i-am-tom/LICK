module LICK.Reduction

import Data.List

import LICK.Expr
import LICK.ProgramType

%default total

||| If two references are not equal, removing one referenced element
||| from the list won't remove the other.
independentRefs
   : (l, r : Elem x xs)
  -> Not (l = r)
  -> Elem x (dropElem xs r)

independentRefs Here Here prf
  = absurd (prf Refl)

independentRefs Here (There later) prf
  = Here

independentRefs (There later) Here prf
  = later

independentRefs (There this) (There that) prf
  = There (independentRefs this that (prf . cong))

||| If different _values_ are referenced, the references are
||| definitely not equal.
independentValues
   : (l : Elem x xs)
  -> (r : Elem y xs)
  -> Not (x = y)
  -> Elem x (dropElem xs r)

independentValues Here Here prf
  = absurd (prf Refl)

independentValues (There later) Here prf
  = later

independentValues Here (There later) prf
  = Here

independentValues (There x) (There later) prf
  = There (independentValues x later prf)


||| Any given abstraction will have a number of variables in scope,
||| as well as a number that are "free". This proof states that we
||| can insert a value between those two partitions and update the
||| given reference if need be.
expandElemContext
   : (bound : Context)
  -> Elem t (bound ++      free)
  -> Elem t (bound ++ a :: free)

expandElemContext [] ref
  = There ref

expandElemContext (_ :: _) Here
  = Here

expandElemContext (_ :: xs) (There later)
  = There (expandElemContext xs later)


||| This is the same as expandElemContext, but works on entire Expr
||| values, rather than individual `Elem` proofs.
expandContext
   : (bound : Context)
  -> Expression (bound ++      free) t
  -> Expression (bound ++ a :: free) t

expandContext bound (Application function argument)
  = Application (expandContext bound function)
                (expandContext bound argument)

expandContext bound (Abstraction parameter body)
  = Abstraction parameter (expandContext (parameter :: bound) body)

expandContext bound (Variable ref)
  = Variable (expandElemContext bound ref)


||| Substitute a given argument into a given body in place of a given
||| reference. There's quite a lot of type-fiddling to be done.
substitute
   : (reference : Elem argType context)
  -> (body      : Expression context programType)
  -> (argument  : Expression (dropElem context reference) argType)
  -> Expression (dropElem context reference) programType

substitute {argType} {programType} reference (Variable referenced) argument
    with (decEq programType argType)
  substitute {argType = programType} reference (Variable referenced) argument
    | (Yes Refl)
          with (decEq referenced reference)
        substitute referenced (Variable referenced) argument
          | (Yes Refl)
          | (Yes Refl)
          = argument
        substitute reference (Variable referenced) argument
          | (Yes Refl)
          | (No contra)
          = Variable (independentRefs referenced reference contra)
  substitute reference (Variable referenced) argument
    | (No contra)
    = Variable (independentValues referenced reference contra)

substitute reference (Abstraction parameter body) argument
  = Abstraction
      parameter
      (substitute (There reference) body (expandContext [] argument))

substitute reference (Application function x) argument
  = Application
      (substitute reference function argument)
      (substitute reference x        argument)


||| Apply β-reduction to the given expression. This won't change
||| the type, but might well change the construction. Any occurrence
||| of an application of an explicit abstraction is reduced by taking
||| the argument and substituting it for the variable in the body of
||| the abstraction.
public export
reduce
   : Expression context programType
  -> Expression context programType

reduce (Abstraction parameter body)
  = Abstraction parameter (reduce body)

reduce (Variable ref)
  = Variable ref

reduce (Application function argument)
  with (reduce function, reduce argument)
    | (Abstraction parameter body, argument')
        = substitute Here body argument'
    | (function', argument')
        = Application function' argument'


--- Tests

Eg0 : Expression context (PFunction PInt PInt)
Eg0 = Abstraction PInt (Variable Here)

Eg1 : Expression context (PFunction PInt PInt)
Eg1 = Abstraction PInt (Application Eg0 (Variable Here))


||| Reduce on irreducible structures is identity.
irreducible
  : reduce (Eg0 {context = []})
  = Eg0 {context = []}

irreducible
  = Refl


||| Reducible structures are reduced.
reducible
  : reduce (Eg1 {context = []})
  = Eg0 {context = []}

reducible
  = Refl

---

||| Example from the blog series.
Test : Expression (x :: context) x
Test {x}
  = Application
      ( Abstraction
          x
          ( Application
              ( Abstraction
                  x
                  ( Application
                      ( Abstraction
                          x
                          ( Variable Here
                          )
                      )
                      ( Variable Here
                      )
                  )
              )
              ( Variable Here
              )
          )
      )
      ( Variable Here
      )

allClear
  : reduce (Test {context = []} {x = PInt})
  = Variable Here

allClear
  = Refl
