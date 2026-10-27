import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue054
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.add_d_tail`.
Recursive calls remain the original extracted calls. -/
def continueAfter (mask_sum : aspis_core.field.QM31) (dc : Array aspis_core.field.QM31 1024#usize) (out : Payload (host_semantic.d_tail_side dc 0#usize)) : Result aspis_core.field.QM31 := do
  let q := out
  let first ← aspis_core.field.QM31.mul_m31 q 512#u32
  let mask_sum1 ← aspis_core.field.QM31.add mask_sum first
  let q1 ← host_semantic.d_tail_side dc 28#usize
  let second ← aspis_core.field.QM31.mul_m31 q1 512#u32
  aspis_core.field.QM31.add mask_sum1 second

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (mask_sum : aspis_core.field.QM31) (dc : Array aspis_core.field.QM31 1024#usize) :
    host_semantic.add_d_tail (mask_sum := mask_sum) (dc := dc) =
      (host_semantic.d_tail_side dc 0#usize >>= fun out => continueAfter (mask_sum := mask_sum) (dc := dc) out) := by
  rw [host_semantic.add_d_tail]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (mask_sum : aspis_core.field.QM31) (dc : Array aspis_core.field.QM31 1024#usize) (out : Payload (host_semantic.d_tail_side dc 0#usize))
    (h : (host_semantic.d_tail_side dc 0#usize) = .ok out) :
    host_semantic.add_d_tail (mask_sum := mask_sum) (dc := dc) = continueAfter (mask_sum := mask_sum) (dc := dc) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (mask_sum : aspis_core.field.QM31) (dc : Array aspis_core.field.QM31 1024#usize) (e : Error)
    (h : (host_semantic.d_tail_side dc 0#usize) = .fail e) :
    host_semantic.add_d_tail (mask_sum := mask_sum) (dc := dc) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (mask_sum : aspis_core.field.QM31) (dc : Array aspis_core.field.QM31 1024#usize)
    (h : (host_semantic.d_tail_side dc 0#usize) = .div) :
    host_semantic.add_d_tail (mask_sum := mask_sum) (dc := dc) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue054
