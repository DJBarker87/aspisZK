import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue071
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `prover.audit_masks`.
Recursive calls remain the original extracted calls. -/
def continueAfter (c1 : Slice (alloc.vec.Vec aspis_core.field.M31)) (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (masks : Array Std.U16 64#usize) (out : Payload (prover.audit_masks_loop0 c1 masks 0#usize 0#usize)) : Result prover.MaskedFixtureAudit := do
  let c1_columns_inactive_balanced := out
  let mask_only_columns_inactive_balanced ←
    prover.audit_masks_loop1 mask_only masks 0#usize 0#usize
  let s ← Aeneas.Std.lift (Array.to_slice d)
  let q ← prover.inactive_sum_k s masks
  let q1 ← aspis_core.field.QM31.ZERO
  let b ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q q1
  let s1 ← Aeneas.Std.lift (Array.to_slice g)
  let q2 ← prover.inactive_sum_k s1 masks
  let b1 ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q2 q1
  let s2 ← Aeneas.Std.lift (Array.to_slice h1_padding)
  let q3 ← prover.inactive_sum_k s2 masks
  let b2 ← aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq q3 q1
  ok
    {
      c1_columns_inactive_balanced,
      mask_only_columns_inactive_balanced,
      d_inactive_balanced := b,
      g_inactive_balanced := b1,
      h1_padding_inactive_balanced := b2,
      h1_total_balanced := true
    }

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation (c1 : Slice (alloc.vec.Vec aspis_core.field.M31)) (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (masks : Array Std.U16 64#usize) :
    prover.audit_masks (c1 := c1) (mask_only := mask_only) (d := d) (g := g) (h1_padding := h1_padding) (masks := masks) =
      (prover.audit_masks_loop0 c1 masks 0#usize 0#usize >>= fun out => continueAfter (c1 := c1) (mask_only := mask_only) (d := d) (g := g) (h1_padding := h1_padding) (masks := masks) out) := by
  rw [prover.audit_masks]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success (c1 : Slice (alloc.vec.Vec aspis_core.field.M31)) (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (masks : Array Std.U16 64#usize) (out : Payload (prover.audit_masks_loop0 c1 masks 0#usize 0#usize))
    (h : (prover.audit_masks_loop0 c1 masks 0#usize 0#usize) = .ok out) :
    prover.audit_masks (c1 := c1) (mask_only := mask_only) (d := d) (g := g) (h1_padding := h1_padding) (masks := masks) = continueAfter (c1 := c1) (mask_only := mask_only) (d := d) (g := g) (h1_padding := h1_padding) (masks := masks) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure (c1 : Slice (alloc.vec.Vec aspis_core.field.M31)) (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (masks : Array Std.U16 64#usize) (e : Error)
    (h : (prover.audit_masks_loop0 c1 masks 0#usize 0#usize) = .fail e) :
    prover.audit_masks (c1 := c1) (mask_only := mask_only) (d := d) (g := g) (h1_padding := h1_padding) (masks := masks) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges (c1 : Slice (alloc.vec.Vec aspis_core.field.M31)) (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) (d : Array aspis_core.field.QM31 1024#usize) (g : Array aspis_core.field.QM31 1024#usize) (h1_padding : Array aspis_core.field.QM31 1024#usize) (masks : Array Std.U16 64#usize)
    (h : (prover.audit_masks_loop0 c1 masks 0#usize 0#usize) = .div) :
    prover.audit_masks (c1 := c1) (mask_only := mask_only) (d := d) (g := g) (h1_padding := h1_padding) (masks := masks) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue071
