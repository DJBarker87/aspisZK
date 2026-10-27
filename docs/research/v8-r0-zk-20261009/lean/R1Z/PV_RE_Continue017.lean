import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue017
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.extra_claims`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (variant : transport.Variant) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (Array aspis_core.field.QM31 29#usize) := do
  let q := out
  let extras := Array.repeat 29#usize q
  host_semantic.extra_claims_loop columns variant a b extras 0#usize

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (variant : transport.Variant) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) :
    host_semantic.extra_claims (columns := columns) (variant := variant) (a := a) (b := b) =
      (aspis_core.field.QM31.ZERO >>= fun out => continueAfter (columns := columns) (variant := variant) (a := a) (b := b) out) := by
  rw [host_semantic.extra_claims]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (variant : transport.Variant) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (out : Payload (aspis_core.field.QM31.ZERO))
    (h : (aspis_core.field.QM31.ZERO) = .ok out) :
    host_semantic.extra_claims (columns := columns) (variant := variant) (a := a) (b := b) = continueAfter (columns := columns) (variant := variant) (a := a) (b := b) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (variant : transport.Variant) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31) (e : Error)
    (h : (aspis_core.field.QM31.ZERO) = .fail e) :
    host_semantic.extra_claims (columns := columns) (variant := variant) (a := a) (b := b) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (variant : transport.Variant) (a : aspis_core.field.QM31) (b : aspis_core.field.QM31)
    (h : (aspis_core.field.QM31.ZERO) = .div) :
    host_semantic.extra_claims (columns := columns) (variant := variant) (a := a) (b := b) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue017
