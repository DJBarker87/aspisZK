-- Original early-return control from the pinned predecessor source representation.
-- Primitive bodies and constants are the actual freshly extracted CT operations.
import PV_B1_254_Funs
set_option autoImplicit false
noncomputable section
namespace PV_B1_PowersOriginal
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev aspis_core.field.wide_exact.WideExact := PV_B1_254.aspis_core.field.wide_exact.WideExact
abbrev aspis_core.field.wide_exact.WideExact.mul := PV_B1_254.aspis_core.field.wide_exact.WideExact.mul
def aspis_core.field.wide_exact.WideExact.ZERO : Result aspis_core.field.wide_exact.WideExact :=
  ok PV_B1_254.aspis_core.field.wide_exact.WideExact.ZERO
def aspis_core.field.wide_exact.WideExact.ONE : Result aspis_core.field.wide_exact.WideExact :=
  ok PV_B1_254.aspis_core.field.wide_exact.WideExact.ONE
/-- [aspis_r1_cost_probe::weights::powers]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/weights.rs', lines 11:1-18:1
    Visibility: public -/
@[rust_loop_body]
def weights.powers_loop.body
  {N : Std.Usize} (x : aspis_core.field.wide_exact.WideExact)
  (out : Array aspis_core.field.wide_exact.WideExact N)
  (p : aspis_core.field.wide_exact.WideExact) (i : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.wide_exact.WideExact N) ×
    aspis_core.field.wide_exact.WideExact × Std.Usize) ((Array
    aspis_core.field.wide_exact.WideExact N) × (Option (Array
    aspis_core.field.wide_exact.WideExact N))))
  := do
  if i < N
  then
    let (_, index_mut_back) ← Array.index_mut_usize out i
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    if i1 = N
    then let out1 := index_mut_back p
         ok (done (out1, some out1))
    else
      let p1 ← aspis_core.field.wide_exact.WideExact.mul p x
      let out1 := index_mut_back p
      ok (cont (out1, p1, i1))
  else ok (done (out, none))

/-- [aspis_r1_cost_probe::weights::powers]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/weights.rs', lines 11:1-18:1
    Visibility: public -/
@[rust_loop]
def weights.powers_loop
  {N : Std.Usize} (x : aspis_core.field.wide_exact.WideExact)
  (out : Array aspis_core.field.wide_exact.WideExact N)
  (p : aspis_core.field.wide_exact.WideExact) (i : Std.Usize) :
  Result ((Array aspis_core.field.wide_exact.WideExact N) × (Option (Array
    aspis_core.field.wide_exact.WideExact N)))
  := do
  loop
    (fun (out1, p1, i1) => weights.powers_loop.body x out1 p1 i1)
    (out, p, i)

/-- [aspis_r1_cost_probe::weights::powers]:
    Source: 'crates/aspis-r1-cost-probe/src/weights.rs', lines 7:0-18:1
    Visibility: public -/
def weights.powers
  (N : Std.Usize) (x : aspis_core.field.wide_exact.WideExact) :
  Result (Array aspis_core.field.wide_exact.WideExact N)
  := do
  let we ← aspis_core.field.wide_exact.WideExact.ZERO
  let out := Array.repeat N we
  let p ← aspis_core.field.wide_exact.WideExact.ONE
  let (out1, pending_return) ← weights.powers_loop x out p 0#usize
  match pending_return with
  | none => ok out1
  | some out2 => ok out2

#print axioms aspis_core.field.wide_exact.WideExact.ZERO
#print axioms aspis_core.field.wide_exact.WideExact.ONE
#print axioms aspis_core.field.wide_exact.WideExact.mul
#print axioms weights.powers_loop.body
#print axioms weights.powers_loop
#print axioms weights.powers
end PV_B1_PowersOriginal
