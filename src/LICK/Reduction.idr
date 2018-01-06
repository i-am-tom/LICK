module LICK.Reduction

import Data.List

import LICK.Expr
import LICK.ProgramType

%default total


||| The constructors don't match.
hereIsNotThere
  : Not (Here = There later)

hereIsNotThere Refl impossible


||| The tails of the `There`s don't match.
tailMismatch
   : Not (      l =       r)
  -> Not (There l = There r)


tailMismatch f Refl
  = f Refl


tailMatch : (l = r) -> (There l = There r)
tailMatch Refl = Refl


||| Decidable equality for Elem. It has been added to the Data.List
||| library, but it needs a version bump.
decEqElem
   : (l, r : Elem x xs)
  -> Dec (l = r)

decEqElem Here Here
  = Yes Refl

decEqElem Here (There later)
  = No hereIsNotThere

decEqElem (There later) Here
  = No (hereIsNotThere . sym)

decEqElem (There l) (There r)
  with (decEqElem l r)
    decEqElem (There r) (There r)
      | Yes Refl
      = Yes Refl
    decEqElem (There l) (There r)
      | No               contra
      = No (tailMismatch contra)


---


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

independentRefs (There later) (There y) prf
  = There (independentRefs later y (prf . cong))


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


||| Because `dropElem` isn't expanded during type-checking, we have
||| to "work around" it a little bit. This proof states that, if I
||| had a reference to an element (_not_ at the head) in a filtered
||| p :: xs, I can produce a reference to an element in a filtered
||| xs with a p at the head.
reassociateDrop
   : Elem x (dropElem (p :: xs) (There idx))
  -> Elem x (p :: dropElem xs idx)

reassociateDrop Here
  = Here

reassociateDrop (There later)
  = There later


||| Any given abstraction will have a number of variables in scope,
||| as well as a number that are "free". This proof states that we
||| can insert a value between those two partitions and update the
||| given reference if need be.
expandElemContext
   : (bound : Context)
  -> Elem t (bound ++      free)
  -> Elem t (bound ++ a :: free)

expandElemContext [] Here
  = There Here

expandElemContext [] (There free)
  = There (There free)

expandElemContext bound@(_ :: _) Here
  = Here

expandElemContext bound@(_ :: xs) (There later)
  = There (expandElemContext xs later)


||| This is the same as expandElemContext, but works on entire Expr
||| values, rather than individual `Elem` proofs.
expandContext
   : (bound : Context)
  -> Expr (bound ++      free) t
  -> Expr (bound ++ a :: free) t

expandContext bound (Var exs)
  = Var (expandElemContext bound exs)

expandContext bound (Abs parameter body)
  = Abs parameter (expandContext (parameter :: bound) body)

expandContext bound (App function argument)
  = App (expandContext bound function)
        (expandContext bound argument)


||| In order to  apply reduction recursively, we need to be able to
||| reassociate the head of the filtered list. This function allows
||| us to transform an expression with a function on the reassociated
||| context.
withReassociatedDrop
   : ( Expr (dropElem (x :: xs) (There this)) a
    -> Expr (dropElem (y :: xs) (There that)) b
     )
  -> Expr (x :: dropElem xs this) a
  -> Expr (y :: dropElem xs that) b

withReassociatedDrop function
  = to . function . from
  where

    from
       : Expr (dropElem (p :: xs) (There idx)) programType
      -> Expr (p :: dropElem xs idx) programType

    from (Var reference)
      = Var (reassociateDrop reference)

    from (Abs parameter body)
      = Abs parameter body

    from (App function argument)
      = App (from function) (from argument)


    to
       : Expr (p :: dropElem xs idx) programType
      -> Expr (dropElem (p :: xs) (There idx)) programType
    to (Var reference)
      = Var reference

    to (Abs parameter body)
      = Abs parameter body

    to (App function argument)
      = App (to function) (to argument)


||| Substitute a given argument into a given body in place of a given
||| reference. There's quite a lot of type-fiddling to be done.
substitute
   : (reference : Elem argType context)
  -> (body      : Expr context programType)
  -> (argument  : Expr (dropElem context reference) argType)
  -> Expr (dropElem context reference) programType

substitute {argType} {programType} reference (Var referenced) argument
    with (decEq programType argType)
  substitute {argType = programType} reference (Var referenced) argument
    | (Yes Refl)
          with (decEqElem referenced reference)
        substitute referenced (Var referenced) argument
          | (Yes Refl)
          | (Yes Refl)
          = argument
        substitute reference (Var referenced) argument
          | (Yes Refl)
          | (No contra)
          = Var (independentRefs referenced reference contra)
  substitute reference (Var referenced) argument
    | (No contra)
    = Var (independentValues referenced reference contra)

substitute reference (Abs parameter body) argument
  = Abs parameter (withReassociatedDrop (substitute (There reference) body)
                                        (expandContext [] argument))

substitute reference (App function x) argument
  = App (substitute reference function argument)
        (substitute reference x        argument)


||| Apply β-reduction to the given expression. This won't change
||| the type, but might well change the construction. Any occurrence
||| of an application of an explicit abstraction is reduced by taking
||| the argument and substituting it for the variable in the body of
||| the abstraction.
public export
reduce
   : Expr context programType
  -> Expr context programType

reduce (Abs parameter body)
  = Abs parameter (reduce body)

reduce (Var x)
  = Var x

reduce (App function argument)
  with (reduce function, reduce argument)
    | (Var reference, argument')
        = App (Var reference) argument'
    | (Abs parameter body, argument')
        = substitute Here body argument'
    | (innerFunction, argument')
        = App innerFunction argument'


--- Tests

Eg0 : Expr context (PFunction PInt PInt)
Eg0 = Abs PInt (Var Here)

Eg1 : Expr context (PFunction PInt PInt)
Eg1 = Abs PInt (App Eg0 (Var Here))


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
