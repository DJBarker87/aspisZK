import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix032
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.opening_batch`.
Recursive calls remain the original extracted calls. -/
def continueAfter (coefficients : Slice (Array aspis_core.field.wide_exact.WideExact
  1024#usize)) (gamma : aspis_core.field.wide_exact.WideExact) (out : Payload (weights.powers 29#usize gamma)) : Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) := do
  let gp := out
  let q :=
    alloc.vec.Vec.with_capacity aspis_core.field.wide_exact.WideExact
      1024#usize
  prover.opening_batch_loop coefficients gp q 0#usize


end R1Z.PV_RE_NoCatchSuffix032
pv_no_catch_binds ProverRwFull.prover.opening_batch
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix032.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix033
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.opening_inactive`.
Recursive calls remain the original extracted calls. -/
def continueAfter (q : Slice aspis_core.field.wide_exact.WideExact) (w : weights.Weights) (out : Payload (aspis_core.field.wide_exact.WideExact.ZERO)) : Result aspis_core.field.wide_exact.WideExact := do
  let inactive := out
  prover.opening_inactive_loop q w inactive 0#usize


end R1Z.PV_RE_NoCatchSuffix033
pv_no_catch_binds ProverRwFull.prover.opening_inactive
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix033.continueAfter
