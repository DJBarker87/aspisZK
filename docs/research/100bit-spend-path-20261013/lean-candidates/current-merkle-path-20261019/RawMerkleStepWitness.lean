import RawMerklePathWalk
import RawMerkleParentCall

/-! A successful emitted round supplies its actual child vector and selected
running digest, rather than assuming a Merkle round relation. -/
set_option autoImplicit false
namespace AspisR1MerklePathChildren.RawMerkleStepWitness
open Aeneas Aeneas.Std Result WP
open RawMerklePathWalk
abbrev Children := Array Digest 8#usize

structure Call {H : Type} (D : Digest32 H) (hash : H) (path : Slice U8)
    (d index : Usize) (node : Digest) (outIndex : Usize) (outNode : Digest) where
  slot : Usize
  children : Children
  remainder : index % 8#usize = ok slot
  slot_value : slot.val = index.val % 8
  slot_bound : slot.val < 8
  selected : children.val[slot.val]? = some node
  child0 : verifier.merkle_child slot node path d 0#usize = ok (RawMerkleParentCall.child children 0)
  child1 : verifier.merkle_child slot node path d 1#usize = ok (RawMerkleParentCall.child children 1)
  child2 : verifier.merkle_child slot node path d 2#usize = ok (RawMerkleParentCall.child children 2)
  child3 : verifier.merkle_child slot node path d 3#usize = ok (RawMerkleParentCall.child children 3)
  child4 : verifier.merkle_child slot node path d 4#usize = ok (RawMerkleParentCall.child children 4)
  child5 : verifier.merkle_child slot node path d 5#usize = ok (RawMerkleParentCall.child children 5)
  child6 : verifier.merkle_child slot node path d 6#usize = ok (RawMerkleParentCall.child children 6)
  child7 : verifier.merkle_child slot node path d 7#usize = ok (RawMerkleParentCall.child children 7)
  parent : merkle.parent_with_digest D hash children = ok outNode
  quotient : index / 8#usize = ok outIndex

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem step_success {H : Type} (D : Digest32 H) (hash : H)
    (path : Slice U8) (d index : Usize) (node : Digest)
    (outIndex : Usize) (outNode : Digest)
    (h : step D hash path d index node = ok (outIndex,outNode)) :
    Nonempty (Call D hash path d index node outIndex outNode) := by
  unfold step at h
  obtain ⟨slot, hslot, h⟩ := bind_success _ _ _ h
  obtain ⟨a0, h0, h⟩ := bind_success _ _ _ h
  obtain ⟨a1, h1, h⟩ := bind_success _ _ _ h
  obtain ⟨a2, h2, h⟩ := bind_success _ _ _ h
  obtain ⟨a3, h3, h⟩ := bind_success _ _ _ h
  obtain ⟨a4, h4, h⟩ := bind_success _ _ _ h
  obtain ⟨a5, h5, h⟩ := bind_success _ _ _ h
  obtain ⟨a6, h6, h⟩ := bind_success _ _ _ h
  obtain ⟨a7, h7, h⟩ := bind_success _ _ _ h
  obtain ⟨nextNode, hp, h⟩ := bind_success _ _ _ h
  obtain ⟨nextIndex, hq, h⟩ := bind_success _ _ _ h
  have hout : (nextIndex,nextNode) = (outIndex,outNode) := Result.ok.inj h
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hout
  have hsval : slot.val = index.val % 8 := by
    have hs := UScalar.rem_spec index (y := 8#usize) (by decide)
    rw [hslot] at hs
    simpa only [WP.spec_ok,UScalar.ofNatCore_val_eq] using hs
  have hslt : slot.val < 8 := by rw [hsval]; exact Nat.mod_lt _ (by decide)
  let children : Children := Array.make 8#usize [a0,a1,a2,a3,a4,a5,a6,a7]
  have hselected : children.val[slot.val]? = some node := by
    have hcases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 ∨ slot.val = 3 ∨
        slot.val = 4 ∨ slot.val = 5 ∨ slot.val = 6 ∨ slot.val = 7 := by omega
    rcases hcases with hv | hv | hv | hv | hv | hv | hv | hv
    · have he : slot = 0#usize := by apply UScalar.eq_of_val_eq; simpa using hv
      have hc : a0 = node := by
        rw [he] at h0
        simp only [verifier.merkle_child,ite_true] at h0
        exact (Result.ok.inj h0).symm
      simpa [children,Array.make,hv] using congrArg some hc
    · have he : slot = 1#usize := by apply UScalar.eq_of_val_eq; simpa using hv
      have hc : a1 = node := by
        rw [he] at h1
        simp only [verifier.merkle_child,ite_true] at h1
        exact (Result.ok.inj h1).symm
      simpa [children,Array.make,hv] using congrArg some hc
    · have he : slot = 2#usize := by apply UScalar.eq_of_val_eq; simpa using hv
      have hc : a2 = node := by
        rw [he] at h2
        simp only [verifier.merkle_child,ite_true] at h2
        exact (Result.ok.inj h2).symm
      simpa [children,Array.make,hv] using congrArg some hc
    · have he : slot = 3#usize := by apply UScalar.eq_of_val_eq; simpa using hv
      have hc : a3 = node := by
        rw [he] at h3
        simp only [verifier.merkle_child,ite_true] at h3
        exact (Result.ok.inj h3).symm
      simpa [children,Array.make,hv] using congrArg some hc
    · have he : slot = 4#usize := by apply UScalar.eq_of_val_eq; simpa using hv
      have hc : a4 = node := by
        rw [he] at h4
        simp only [verifier.merkle_child,ite_true] at h4
        exact (Result.ok.inj h4).symm
      simpa [children,Array.make,hv] using congrArg some hc
    · have he : slot = 5#usize := by apply UScalar.eq_of_val_eq; simpa using hv
      have hc : a5 = node := by
        rw [he] at h5
        simp only [verifier.merkle_child,ite_true] at h5
        exact (Result.ok.inj h5).symm
      simpa [children,Array.make,hv] using congrArg some hc
    · have he : slot = 6#usize := by apply UScalar.eq_of_val_eq; simpa using hv
      have hc : a6 = node := by
        rw [he] at h6
        simp only [verifier.merkle_child,ite_true] at h6
        exact (Result.ok.inj h6).symm
      simpa [children,Array.make,hv] using congrArg some hc
    · have he : slot = 7#usize := by apply UScalar.eq_of_val_eq; simpa using hv
      have hc : a7 = node := by
        rw [he] at h7
        simp only [verifier.merkle_child,ite_true] at h7
        exact (Result.ok.inj h7).symm
      simpa [children,Array.make,hv] using congrArg some hc
  refine ⟨⟨slot,children,hslot,hsval,hslt,hselected,?_,?_,?_,?_,?_,?_,?_,?_,hp,hq⟩⟩
  · simpa [RawMerkleParentCall.child,children,Array.make] using h0
  · simpa [RawMerkleParentCall.child,children,Array.make] using h1
  · simpa [RawMerkleParentCall.child,children,Array.make] using h2
  · simpa [RawMerkleParentCall.child,children,Array.make] using h3
  · simpa [RawMerkleParentCall.child,children,Array.make] using h4
  · simpa [RawMerkleParentCall.child,children,Array.make] using h5
  · simpa [RawMerkleParentCall.child,children,Array.make] using h6
  · simpa [RawMerkleParentCall.child,children,Array.make] using h7

#print axioms step_success
end AspisR1MerklePathChildren.RawMerkleStepWitness
