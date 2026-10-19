import AspisR1MerklePathChildren.Funs

/-! Exact digest-call equation for the source parent helper. The parent body
is unchanged in the explicit-child candidate. Reuses the standard generic
array-index argument from RawPoseidonExternalRowReads without importing the
unrelated field/Poseidon proof closure. -/
set_option autoImplicit false
namespace AspisR1MerklePathChildren.RawMerkleParentCall
open Aeneas Aeneas.Std Result

abbrev Digest := Array U8 32#usize
abbrev Children := Array Digest 8#usize

def child (children : Children) (i : Fin 8) : Digest :=
  children.val[i.val]'(by simpa [children.property] using i.isLt)

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

def parentParts (children : Children) : Slice (Slice U8) :=
  Array.to_slice (Array.make 9#usize
    [Array.to_slice (Array.make 1#usize [24#u8]),
     Array.to_slice (child children 0),Array.to_slice (child children 1),
     Array.to_slice (child children 2),Array.to_slice (child children 3),
     Array.to_slice (child children 4),Array.to_slice (child children 5),
     Array.to_slice (child children 6),Array.to_slice (child children 7)])

/-- The actual emitted helper is exactly one digest call on these nine parts,
preserving its successful, error and divergence results. -/
theorem parent_equation {H : Type} (D : Digest32 H) (hash : H) (children : Children) :
    merkle.parent_with_digest D hash children = D.digest hash (parentParts children) := by
  have h0 := array_index_usize_ok children 0#usize (by decide)
  have h1 := array_index_usize_ok children 1#usize (by decide)
  have h2 := array_index_usize_ok children 2#usize (by decide)
  have h3 := array_index_usize_ok children 3#usize (by decide)
  have h4 := array_index_usize_ok children 4#usize (by decide)
  have h5 := array_index_usize_ok children 5#usize (by decide)
  have h6 := array_index_usize_ok children 6#usize (by decide)
  have h7 := array_index_usize_ok children 7#usize (by decide)
  simp only [merkle.parent_with_digest,h0,h1,h2,h3,h4,h5,h6,h7,lift,bind_tc_ok]
  rfl

/-- Successful source parent hashing supplies its own exact grouped digest
success, rather than an independently postulated address or answer. -/
theorem parent_success {H : Type} (D : Digest32 H) (hash : H)
    (children : Children) (out : Digest)
    (h : merkle.parent_with_digest D hash children = .ok out) :
    D.digest hash (parentParts children) = .ok out := by
  rw [← parent_equation]
  exact h

#print axioms parent_equation
#print axioms parent_success
end AspisR1MerklePathChildren.RawMerkleParentCall
