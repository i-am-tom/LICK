module LICK.Expr

import LICK.ProgramType

import Data.List

%default total


||| A context is just the list of types for the defined variables.
||| The actual encoding is something like De Bruijn indices, but
||| we use `Elem type context` instead of `Nat`!
public export
Context : Type
Context = List ProgramType


||| Here is our vocabulary for expressing programs. We define our
||| constructors and use the GADT to manage the changes to the
||| context.
public export
data Expr : (context : Context) -> ProgramType -> Type where

  ||| A reference to a bound variable. Free variables are expressed
  ||| by using an explicit initial context.
  Var : (reference : Elem programType context)
     -> Expr context programType

  ||| A function abstraction from a value of the given parameter
  ||| type. The body is an expression for which the parameter is in
  ||| scope.
  Abs : (parameter : ProgramType)
     -> (body      : Expr (parameter :: context) programType)
     -> Expr context (PFunction parameter programType)

  ||| Function application. Apply the given function-typed expression
  ||| to an expression of the parameter type.
  App : (function : Expr context (PFunction parameter return))
     -> (argument : Expr context parameter)
     -> Expr context return
