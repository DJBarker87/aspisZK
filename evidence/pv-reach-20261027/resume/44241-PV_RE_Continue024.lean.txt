import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue024
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_sumcheck.merge_evaluations`.
Recursive calls remain the original extracted calls. -/
def continueAfter (evaluations : Slice (core.result.Result aspis_core.field.QM31
  r1_wire.Error)) (assignments : Std.Usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (core.result.Result (Array aspis_core.field.QM31 28#usize)
    r1_wire.Error) := do
  let q := out
  let values := Array.repeat 28#usize q
  let count := Slice.len evaluations
  let (values1, pending_return) ←
    host_sumcheck.merge_evaluations_loop evaluations assignments values count
      0#usize
  match pending_return with
  | none => ok (core.result.Result.Ok values1)
  | some r => ok r

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (evaluations : Slice (core.result.Result aspis_core.field.QM31
  r1_wire.Error)) (assignments : Std.Usize) :
    host_sumcheck.merge_evaluations (evaluations := evaluations) (assignments := assignments) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (evaluations := evaluations) (assignments := assignments) out) := by
  rw [host_sumcheck.merge_evaluations]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (evaluations : Slice (core.result.Result aspis_core.field.QM31
  r1_wire.Error)) (assignments : Std.Usize) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_sumcheck.merge_evaluations (evaluations := evaluations) (assignments := assignments) = continueAfter (evaluations := evaluations) (assignments := assignments) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (evaluations : Slice (core.result.Result aspis_core.field.QM31
  r1_wire.Error)) (assignments : Std.Usize) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_sumcheck.merge_evaluations (evaluations := evaluations) (assignments := assignments) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (evaluations : Slice (core.result.Result aspis_core.field.QM31
  r1_wire.Error)) (assignments : Std.Usize)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_sumcheck.merge_evaluations (evaluations := evaluations) (assignments := assignments) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue024
