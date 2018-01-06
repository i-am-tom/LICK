module LICK.ProgramType

%default total


||| The primitive types within the language are given explicitly with
||| this data type. User-defined types will be built from these.
public export
data ProgramType : Type where

  ||| A function between two types.
  PFunction
     : (input  : ProgramType)
    -> (output : ProgramType)
    -> ProgramType

  ||| The unit type.
  PUnit : ProgramType


||| If the domains don't match, the functions definitely don't.
domainsDoNotMatch
   : Not (          i   =           i'   )
  -> Not (PFunction i o = PFunction i' o')

domainsDoNotMatch f Refl
  = f Refl


||| If the codomains don't match, the functions definitely don't.
codomainsDoNotMatch
   : Not (            o =              o')
  -> Not (PFunction i o = PFunction i' o')

codomainsDoNotMatch f Refl
  = f Refl


||| A function is not a unit.
functionIsNotUnit
  : Not (PFunction i o = PUnit)

functionIsNotUnit Refl impossible


||| Decidable equality on program types.
public export
implementation DecEq ProgramType where
  decEq PUnit PUnit
    = Yes Refl
  decEq PUnit (PFunction i o)
    = No (functionIsNotUnit . sym)
  decEq (PFunction i o) PUnit
    = No functionIsNotUnit
  decEq (PFunction i o) (PFunction i' o')
    with (decEq i i', decEq o o')
      decEq (PFunction i o) (PFunction i o)
        | (Yes Refl, Yes Refl) = Yes Refl
      decEq (PFunction i _) (PFunction i' _)
        | (No contra, _) = No (domainsDoNotMatch contra)
      decEq (PFunction _ o) (PFunction _ o')
        | (_, No contra) = No (codomainsDoNotMatch contra)
