import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix030
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.inactive_sum_k`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let sum := out
  prover.inactive_sum_k_loop values masks sum 0#usize


end R1Z.PV_RE_NoCatchSuffix030
pv_no_catch_binds ProverRwFull.prover.inactive_sum_k
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix030.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix031
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.inactive_sum_m31`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Slice aspis_core.field.M31) (masks : Array Std.U16 64#usize) (out : Payload (aspis_core.field.M31.ZERO)) : Result aspis_core.field.M31 := do
  let sum := out
  prover.inactive_sum_m31_loop values masks sum 0#usize


end R1Z.PV_RE_NoCatchSuffix031
pv_no_catch_binds ProverRwFull.prover.inactive_sum_m31
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix031.continueAfter
