import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue018
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.initial_mask_sum`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let sum := out
  host_semantic.initial_mask_sum_loop columns sum 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) :
    host_semantic.initial_mask_sum (columns := columns) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (columns := columns) out) := by
  rw [host_semantic.initial_mask_sum]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_semantic.initial_mask_sum (columns := columns) = continueAfter (columns := columns) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_semantic.initial_mask_sum (columns := columns) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_semantic.initial_mask_sum (columns := columns) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue018
