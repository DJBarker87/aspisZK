import WireTx2LeafBodies
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2.WireTx2

def leafParts (tag : U8) (values : Slice U8) (salt : Bytes32) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [
    Array.to_slice (Array.make 2#usize [16#u8, tag]), values, Array.to_slice salt])

/-- Named backend correspondence premise, not an axiom or a fact supplied by
stage2 extraction: the private-leaf implementation is external there. -/
def LeafDigestLaw (ops : LeafOps) : Prop :=
  ∀ {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (tag : U8) (values : Slice U8) (salt : Bytes32),
    ops.leaf D hash tag values salt = D.digest hash (leafParts tag values salt)

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Every successful emitted batch-leaf call supplies exactly one of the three
D79 leaf grammars to its backend. Slice widths are derived, not assumed. -/
theorem batch_leaf_typed (ops : LeafOps)
    (c1 : ops.c1Tag = ok 113#u8) (c2 : ops.c2Tag = ok 241#u8)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (tree : Usize) (q : Slice U8) (out : Bytes32)
    (h : verifier.candidate.batch_leafWithWireOps ops D hash tree q = ok out) :
    ∃ (tag : U8) (values : Slice U8) (salt : Bytes32),
      ops.leaf D hash tag values salt = ok out ∧ TypedInput (leafParts tag values salt) := by
  unfold verifier.candidate.batch_leafWithWireOps at h
  split at h
  · obtain ⟨saltBytes, _, h⟩ := bind_success _ _ _ h
    obtain ⟨salt, _, h⟩ := bind_success _ _ _ h
    obtain ⟨values, hv, h⟩ := bind_success _ _ _ h
    rw [c1] at h
    simp only [bind_tc_ok] at h
    have hw : values.val.length = 480 := prefix_width q values 480#usize hv
    exact ⟨113#u8, values, salt, h, .leaf _ _ _ (Or.inl ⟨rfl, hw⟩)⟩
  · obtain ⟨saltBytes, _, h⟩ := bind_success _ _ _ h
    obtain ⟨salt, _, h⟩ := bind_success _ _ _ h
    obtain ⟨values, hv, h⟩ := bind_success _ _ _ h
    rw [c2] at h
    simp only [bind_tc_ok] at h
    have hw0 := range_width q values 480#usize 608#usize hv
    have h480 : (480#usize).val = 480 := rfl
    have h608 : (608#usize).val = 608 := rfl
    rw [h480, h608] at hw0
    have hw : values.val.length = 128 := by omega
    exact ⟨241#u8, values, salt, h, .leaf _ _ _ (Or.inr ⟨Or.inl rfl, hw⟩)⟩
  · obtain ⟨saltBytes, _, h⟩ := bind_success _ _ _ h
    obtain ⟨salt, _, h⟩ := bind_success _ _ _ h
    obtain ⟨values, hv, h⟩ := bind_success _ _ _ h
    have hw0 := range_width q values 672#usize 800#usize hv
    have h672 : (672#usize).val = 672 := rfl
    have h800 : (800#usize).val = 800 := rfl
    rw [h672, h800] at hw0
    have hw : values.val.length = 128 := by omega
    exact ⟨114#u8, values, salt, h, .leaf _ _ _ (Or.inr ⟨Or.inr rfl, hw⟩)⟩

theorem batch_leaf_digest_typed (ops : LeafOps) (law : LeafDigestLaw ops)
    (c1 : ops.c1Tag = ok 113#u8) (c2 : ops.c2Tag = ok 241#u8)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (tree : Usize) (q : Slice U8) (out : Bytes32)
    (h : verifier.candidate.batch_leafWithWireOps ops D hash tree q = ok out) :
    ∃ parts, D.digest hash parts = ok out ∧ TypedInput parts := by
  obtain ⟨tag, values, salt, hcall, htyped⟩ := batch_leaf_typed ops c1 c2 D hash tree q out h
  exact ⟨leafParts tag values salt, (law D hash tag values salt) ▸ hcall, htyped⟩
#print axioms bind_success
#print axioms batch_leaf_typed
#print axioms batch_leaf_digest_typed
end AspisR1Stage2.WireTx2
