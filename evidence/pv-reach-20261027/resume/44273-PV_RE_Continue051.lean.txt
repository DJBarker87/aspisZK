import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue051
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_commitment.validate_commitment_lanes`.
Recursive calls remain the original extracted calls. -/
def continueAfter (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) (lanes : Slice Std.Usize) (out : Payload (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize)) : Result (core.result.Result Unit aspis_core.r0.Error) := do
  let pending_return := out
  match pending_return with
  | none => ok (core.result.Result.Ok ())
  | some r => ok r

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) (lanes : Slice Std.Usize) :
    host_commitment.validate_commitment_lanes (messages := messages) (lanes := lanes) =
      (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize >>= fun out => continueAfter (messages := messages) (lanes := lanes) out) := by
  rw [host_commitment.validate_commitment_lanes]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) (lanes : Slice Std.Usize) (out : Payload (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize))
    (h : (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize) = .ok out) :
    host_commitment.validate_commitment_lanes (messages := messages) (lanes := lanes) = continueAfter (messages := messages) (lanes := lanes) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) (lanes : Slice Std.Usize) (e : Error)
    (h : (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize) = .fail e) :
    host_commitment.validate_commitment_lanes (messages := messages) (lanes := lanes) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize)) (lanes : Slice Std.Usize)
    (h : (host_commitment.validate_commitment_lanes_loop messages lanes 0#usize) = .div) :
    host_commitment.validate_commitment_lanes (messages := messages) (lanes := lanes) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue051
