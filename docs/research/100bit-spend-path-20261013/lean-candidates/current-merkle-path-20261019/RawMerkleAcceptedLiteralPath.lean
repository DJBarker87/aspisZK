import RawMerkleAcceptedWalk
import RawMerkleStepWitness
import RawMerkleParentBytes

/-! Finite actual-parent-call interface for the explicit-child checker.
Checker acceptance supplies an ideal authentication path at the public base-8
positions. Oracle interpretation is required only at its reached parent calls.
This is not a production-candidate equivalence or global-log inclusion result. -/
set_option autoImplicit false
namespace AspisR1MerklePathChildren.RawMerkleAcceptedLiteralPath
open Aeneas Aeneas.Std Result WP
open RawMerklePathWalk
open RawMerkleParentCall (Children child)
open RawMerkleParentBytes (decodeDigest decodeChildren)
open AspisR1.Merkle32Path (Path foldPath fillChild nodeInput)

structure ParentCall {H : Type} (D : Digest32 H) (hash : H) where
  children : Children
  out : Digest
  success : merkle.parent_with_digest D hash children = ok out

def Consistent {H : Type} {D : Digest32 H} {hash : H}
    (oracle : List (Fin 256) → AspisR1.Merkle32Path.Digest)
    (calls : List (ParentCall D hash)) : Prop :=
  ∀ c ∈ calls, decodeDigest c.out = oracle (nodeInput (decodeChildren c.children))

def positions : Nat → Nat → List Nat
  | _, 0 => []
  | index, n+1 => index % 8 :: positions (index / 8) n

private theorem selected_children {H : Type} {D : Digest32 H} {hash : H}
    {path : Slice U8} {d index : Usize} {node : Digest}
    {outIndex : Usize} {outNode : Digest}
    (c : RawMerkleStepWitness.Call D hash path d index node outIndex outNode) :
    fillChild ⟨c.slot.val,c.slot_bound⟩ (decodeChildren c.children) (decodeDigest node) =
      decodeChildren c.children := by
  have hi : c.slot.val < c.children.val.length := by
    simpa [c.children.property] using c.slot_bound
  have hs := c.selected
  rw [List.getElem?_eq_getElem hi] at hs
  have hraw := Option.some.inj hs
  have hdecoded : decodeChildren c.children ⟨c.slot.val,c.slot_bound⟩ = decodeDigest node := by
    apply congrArg decodeDigest
    simpa only [child] using hraw
  funext i
  by_cases he : i = ⟨c.slot.val,c.slot_bound⟩
  · subst i; simp [fillChild,hdecoded]
  · simp [fillChild,he]

/-- One witness sequence, derived from actual success, works for every oracle
consistent with its own finite reached parent calls. -/
theorem walk_literal_path {H : Type} (D : Digest32 H) (hash : H) (path : Slice U8)
    {count depth : Nat} {index outIndex : Usize} {node outNode : Digest}
    (hw : Walk D hash path count depth index node outIndex outNode) :
    ∃ (calls : List (ParentCall D hash)) (slots : List (Fin 8)) (p : Path slots),
      calls.length = count ∧ slots.map Fin.val = positions index.val count ∧
      ∀ oracle, Consistent oracle calls →
        foldPath oracle p (decodeDigest node) = decodeDigest outNode := by
  induction hw with
  | nil depth index node =>
    refine ⟨[],[],.nil,rfl,rfl,?_⟩
    intro oracle _
    rfl
  | @cons count depth index index1 index2 node node1 node2 d hd hs tail ih =>
    obtain ⟨c⟩ := RawMerkleStepWitness.step_success D hash path d index node index1 node1 hs
    rcases ih with ⟨calls,slots,p,hcount,hpositions,hfold⟩
    let pc : ParentCall D hash := ⟨c.children,node1,c.parent⟩
    let k : Fin 8 := ⟨c.slot.val,c.slot_bound⟩
    have hquotient : index1.val = index.val / 8 := by
      obtain ⟨q,hq,hval⟩ := UScalar.div_spec index (y := 8#usize) (by decide)
      have he : q = index1 := Result.ok.inj (hq.symm.trans c.quotient)
      subst q
      simpa only [UScalar.ofNatCore_val_eq] using hval
    refine ⟨pc::calls,k::slots,.cons (decodeChildren c.children) p,?_,?_,?_⟩
    · simp only [List.length_cons,hcount]
    · simp only [List.map_cons,hpositions,positions,hquotient]
      change c.slot.val :: positions (index.val / 8) count = _
      rw [c.slot_value]
    · intro oracle hcons
      have hp : decodeDigest node1 = oracle (nodeInput (decodeChildren c.children)) :=
        hcons pc (by simp)
      have htail : Consistent oracle calls := by
        intro q hq
        exact hcons q (by simp only [List.mem_cons]; exact Or.inr hq)
      simp only [foldPath]
      rw [selected_children c,← hp]
      exact hfold oracle htail

/-- The successful Boolean checker supplies all six positions, actual parent
calls and the root equality; only finite oracle consistency remains an input. -/
theorem accepted_literal_path {H : Type} (D : Digest32 H) (hash : H)
    (root : Digest) (index : Usize) (node : Digest) (path : Slice U8)
    (h : verifier.merkle_path D hash root index node path = ok true) :
    ∃ (calls : List (ParentCall D hash)) (slots : List (Fin 8)) (p : Path slots),
      calls.length = 6 ∧ slots.map Fin.val = positions index.val 6 ∧
      ∀ oracle, Consistent oracle calls →
        foldPath oracle p (decodeDigest node) = decodeDigest root := by
  exact walk_literal_path D hash path (RawMerkleAcceptedWalk.accepted_walk D hash root index node path h)

#print axioms walk_literal_path
#print axioms accepted_literal_path
end AspisR1MerklePathChildren.RawMerkleAcceptedLiteralPath
