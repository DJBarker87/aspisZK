import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue030
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.inactive_sum_k`.
Recursive calls remain the original extracted calls. -/
def continueAfter (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let sum := out
  prover.inactive_sum_k_loop values masks sum 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize) :
    prover.inactive_sum_k (values := values) (masks := masks) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (values := values) (masks := masks) out) := by
  rw [prover.inactive_sum_k]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    prover.inactive_sum_k (values := values) (masks := masks) = continueAfter (values := values) (masks := masks) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    prover.inactive_sum_k (values := values) (masks := masks) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (values : Slice aspis_core.field.QM31) (masks : Array Std.U16 64#usize)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    prover.inactive_sum_k (values := values) (masks := masks) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue030
