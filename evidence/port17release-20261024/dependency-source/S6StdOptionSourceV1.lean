import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error





namespace AspisS6StdOptionMethods
/-- Exact discriminants from the included current Rust Option LLBC declaration.
The backend uses Lean Option but omits this required generated instance. -/
instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant
    | none => 0#isize
    | some _ => 1#isize



 def core.option.Option.ok_or {T : Type} {E : Type} (self : Option T) (err : E) : Result (core.result.Result T E) := do
                                                                match self with
                                                                | none => ok (core.result.Result.Err err)
                                                                | some v => ok (core.result.Result.Ok v)


 def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) (self : Option T) (other : Option T) : Result Bool := do
                                                                                                             match self with
                                                                                                             | none => let other1 := read_discriminant other
                                                                                                                       ok (other1 = 0#isize)
                                                                                                             | some l => match other with
                                                                                                                         | none => ok false
                                                                                                                         | some r => cmpPartialEqInst.eq l r


def option_ok_or {T : Type} {E : Type} (value : Option T) (error : E) : Result (core.result.Result T E) := do
  core.option.Option.ok_or value error


def option_eq {T : Type} (corecmpPartialEqInst : core.cmp.PartialEq T T) (a : Option T) (b : Option T) : Result Bool := do
  core.option.Option.Insts.CoreCmpPartialEqOption.eq corecmpPartialEqInst a b

end AspisS6StdOptionMethods

#print axioms AspisS6StdOptionMethods.option_ok_or
#print axioms AspisS6StdOptionMethods.option_eq
