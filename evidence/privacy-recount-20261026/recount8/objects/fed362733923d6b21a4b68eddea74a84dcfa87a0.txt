import R1Z.ProverRwFullTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwDictionaryOptionSource
local instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant := fun x => match x with | none => 0#isize | some _ => 1#isize

def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

def core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type} (self : Option T) :
  Result (core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T)
  := do
  match self with
  | none => ok (core.ops.control_flow.ControlFlow.Break none)
  | some v => ok (core.ops.control_flow.ControlFlow.Continue v)

def
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
  (T : Type) (o : Option core.convert.Infallible) : Result (Option T) := do
  let i := read_discriminant o
  massert (i = 0#isize)
  ok none
end R1Z.ProverRwDictionaryOptionSource
