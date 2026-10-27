import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue028
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_tree.append_levels`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (hash : H) (levels : alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) (depth : Std.Usize) (out : Payload (multiproof.LEAF_BITS)) : Result (alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) := do
  let i := out
  let i1 ← Aeneas.Std.lift (UScalar.cast .Usize i)
  if depth = i1
  then ok levels
  else
    let v ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec
        (Array Std.U8 32#usize))) levels depth
    let s := alloc.vec.Vec.deref v
    let next ← host_tree.next_level aspis_coredigestDigest32Inst hash s
    let levels1 ← alloc.vec.Vec.push levels next
    let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add depth 1#usize)
    host_tree.append_levels aspis_coredigestDigest32Inst hash levels1 i2

/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (hash : H) (levels : alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) (depth : Std.Usize) :
    host_tree.append_levels (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (hash := hash) (levels := levels) (depth := depth) =
      (multiproof.LEAF_BITS >>= fun out => continueAfter (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (hash := hash) (levels := levels) (depth := depth) out) := by
  rw [host_tree.append_levels]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (hash : H) (levels : alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) (depth : Std.Usize) (out : Payload (multiproof.LEAF_BITS))
    (h : (multiproof.LEAF_BITS) = .ok out) :
    host_tree.append_levels (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (hash := hash) (levels := levels) (depth := depth) = continueAfter (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (hash := hash) (levels := levels) (depth := depth) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (hash : H) (levels : alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) (depth : Std.Usize) (e : Error)
    (h : (multiproof.LEAF_BITS) = .fail e) :
    host_tree.append_levels (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (hash := hash) (levels := levels) (depth := depth) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (hash : H) (levels : alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) (depth : Std.Usize)
    (h : (multiproof.LEAF_BITS) = .div) :
    host_tree.append_levels (H := H) (aspis_coredigestDigest32Inst := aspis_coredigestDigest32Inst) (hash := hash) (levels := levels) (depth := depth) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue028
