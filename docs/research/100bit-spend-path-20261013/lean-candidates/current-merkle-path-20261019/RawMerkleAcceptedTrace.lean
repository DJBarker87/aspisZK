import RawMerkleAcceptedLiteralPath

/-! Ordered literal parent-call trace under finite oracle consistency.
The remaining global-log embedding is explicit, not inferred from successful
pure digest equations. This remains the explicit-child source candidate. -/
set_option autoImplicit false
namespace AspisR1MerklePathChildren.RawMerkleAcceptedTrace
open Aeneas Aeneas.Std Result WP
open RawMerklePathWalk
open RawMerkleParentCall (Children child parentParts)
open RawMerkleParentBytes (decodeDigest decodeChildren flattenParts parent_literal_bytes)
open RawMerkleAcceptedLiteralPath (ParentCall Consistent positions)
open AspisR1.Merkle32Path (Path foldPath fillChild nodeInput inputTrace)

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

theorem walk_literal_trace {H : Type} (D : Digest32 H) (hash : H) (path : Slice U8)
    {count depth : Nat} {index outIndex : Usize} {node outNode : Digest}
    (hw : Walk D hash path count depth index node outIndex outNode) :
    ∃ (calls : List (ParentCall D hash)) (slots : List (Fin 8)) (p : Path slots),
      calls.length = count ∧ slots.map Fin.val = positions index.val count ∧
      ∀ oracle, Consistent oracle calls →
        foldPath oracle p (decodeDigest node) = decodeDigest outNode ∧
        calls.map (fun c => nodeInput (decodeChildren c.children)) =
          AspisR1.Merkle32Path.inputTrace oracle p (decodeDigest node) := by
  induction hw with
  | nil depth index node =>
    refine ⟨[],[],.nil,rfl,rfl,?_⟩
    intro oracle _
    exact ⟨rfl,rfl⟩
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
      simp only [foldPath,AspisR1.Merkle32Path.inputTrace,k,selected_children c,← hp]
      refine ⟨(hfold oracle htail).1,?_⟩
      simpa only [List.map_cons,pc] using
        congrArg (List.cons (nodeInput (decodeChildren c.children))) (hfold oracle htail).2

def rawLog {H : Type} {D : Digest32 H} {hash : H} (calls : List (ParentCall D hash)) :
    List (List (Fin 256) × AspisR1.Merkle32Path.Digest) :=
  calls.map (fun c => (flattenParts (parentParts c.children),decodeDigest c.out))

theorem rawLog_image {H : Type} {D : Digest32 H} {hash : H}
    (calls : List (ParentCall D hash))
    (oracle : List (Fin 256) → AspisR1.Merkle32Path.Digest)
    (hc : Consistent oracle calls) :
    rawLog calls = calls.map (fun c => (nodeInput (decodeChildren c.children),
      oracle (nodeInput (decodeChildren c.children)))) := by
  unfold rawLog
  apply List.map_congr_left
  intro c hmem
  rw [parent_literal_bytes,hc c hmem]

theorem consistent_of_globalLog {H : Type} {D : Digest32 H} {hash : H}
    (calls : List (ParentCall D hash))
    (oracle : List (Fin 256) → AspisR1.Merkle32Path.Digest)
    (tr : List (List (Fin 256) × AspisR1.Merkle32Path.Digest))
    (hsub : ∀ q ∈ rawLog calls, q ∈ tr)
    (hglobal : ∀ q ∈ tr, q.2 = oracle q.1) : Consistent oracle calls := by
  intro c hc
  have hm : (flattenParts (parentParts c.children),decodeDigest c.out) ∈ tr :=
    hsub _ (List.mem_map.mpr ⟨c,hc,rfl⟩)
  have he := hglobal _ hm
  simpa only [parent_literal_bytes] using he

theorem accepted_global_trace {H : Type} (D : Digest32 H) (hash : H)
    (root : Digest) (index : Usize) (node : Digest) (path : Slice U8)
    (h : verifier.merkle_path D hash root index node path = ok true) :
    ∃ (calls : List (ParentCall D hash)) (slots : List (Fin 8)) (p : Path slots),
      calls.length = 6 ∧ slots.map Fin.val = positions index.val 6 ∧
      ∀ (oracle : List (Fin 256) → AspisR1.Merkle32Path.Digest)
        (tr : List (List (Fin 256) × AspisR1.Merkle32Path.Digest)),
        (∀ q ∈ rawLog calls, q ∈ tr) →
        (∀ q ∈ tr, q.2 = oracle q.1) →
        foldPath oracle p (decodeDigest node) = decodeDigest root ∧
        rawLog calls = (inputTrace oracle p (decodeDigest node)).map
          (fun input => (input,oracle input)) := by
  obtain ⟨calls,slots,p,hcount,hpositions,htrace⟩ :=
    walk_literal_trace D hash path (RawMerkleAcceptedWalk.accepted_walk D hash root index node path h)
  refine ⟨calls,slots,p,hcount,hpositions,?_⟩
  intro oracle tr hsub hglobal
  have hc := consistent_of_globalLog calls oracle tr hsub hglobal
  obtain ⟨hfold,hinputs⟩ := htrace oracle hc
  refine ⟨hfold,?_⟩
  rw [rawLog_image calls oracle hc,← hinputs,List.map_map]
  rfl

#print axioms walk_literal_trace
#print axioms rawLog_image
#print axioms consistent_of_globalLog
#print axioms accepted_global_trace
end AspisR1MerklePathChildren.RawMerkleAcceptedTrace
