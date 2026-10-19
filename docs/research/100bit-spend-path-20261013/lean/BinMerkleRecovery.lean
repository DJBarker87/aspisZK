import BinMerkleTable

/-! Mirrors `MerkleRecovery.lean`; see design/BIN-COMMITMENT-MODEL-20261019.md for line pins.
 A finite recorded-node walk either recovers an authenticated digest,
exposes a collision with a recorded node, or encounters a missing preimage
whose digest is a root/child target already present in the fixed input.
The table's correspondence to a causal oracle prefix and the probability
of the missing-preimage event are not asserted here. -/
set_option autoImplicit false
namespace AspisR1.BinMerkleRecovery

open BinMerkle32Path BinMerkleTable

def nodeInputs (nodes : Nodes) : List (List Byte) :=
  nodes.map fun q => nodeInput q.1

def Consistent (hash : List Byte → Digest) (nodes : Nodes) : Prop :=
  ∀ cs d, (cs, d) ∈ nodes → hash (nodeInput cs) = d

def MissingHit (hash : List Byte → Digest) (nodes : Nodes)
    (root : Digest) (trace : List (List Byte)) : Prop :=
  ∃ input ∈ trace, hash input ∈ targets nodes root ∧ lookup nodes (hash input) = none

theorem walk_reconstruct (hash : List Byte → Digest) (nodes : Nodes)
    (hconsistent : Consistent hash nodes) :
    ∀ {slots : List (Fin 2)} (path : Path slots) (current : Digest),
      CollisionFreeOn hash (nodeInputs nodes) (inputTrace hash path current) →
      ¬ MissingHit hash nodes (foldPath hash path current) (inputTrace hash path current) →
      walk nodes slots (foldPath hash path current) = some current := by
  intro slots
  induction slots with
  | nil =>
      intro path current _ _
      cases path
      rfl
  | cons slot slots ih =>
      intro path current hfree hmissing
      cases path with
      | cons siblings tail =>
          let actual := nodeInput (fillChild slot siblings current)
          let parent := hash actual
          let root := foldPath hash tail parent
          have htailfree : CollisionFreeOn hash (nodeInputs nodes)
              (inputTrace hash tail parent) := by
            intro left hl right hr heq
            apply hfree left hl right _ heq
            exact List.mem_cons_of_mem actual hr
          have htailmissing : ¬ MissingHit hash nodes root (inputTrace hash tail parent) := by
            rintro ⟨input, hin, htarget, hnone⟩
            exact hmissing ⟨input, List.mem_cons_of_mem actual hin, htarget, hnone⟩
          have hwalk : walk nodes slots root = some parent :=
            ih tail parent htailfree htailmissing
          have htarget : parent ∈ targets nodes root :=
            walk_mem_targets nodes slots root parent hwalk
          have hlookup : lookup nodes parent ≠ none := by
            intro hnone
            exact hmissing ⟨actual, List.mem_cons_self .., htarget, hnone⟩
          cases hl : lookup nodes parent with
          | none => exact False.elim (hlookup hl)
          | some cs =>
              have hentry : (cs, parent) ∈ nodes := lookup_mem hl
              have hrecorded : nodeInput cs ∈ nodeInputs nodes :=
                List.mem_map.mpr ⟨(cs, parent), hentry, rfl⟩
              have heq : nodeInput cs = actual :=
                hfree (nodeInput cs) hrecorded actual (List.mem_cons_self ..)
                  (hconsistent cs parent hentry)
              have hcs : cs = fillChild slot siblings current := nodeInput_injective heq
              change (walk nodes slots root).bind
                (fun d => (lookup nodes d).map fun children => children slot) = some current
              rw [hwalk]
              simp [hl, hcs, fillChild]

theorem recover_or_bad (hash : List Byte → Digest) (nodes : Nodes)
    (hconsistent : Consistent hash nodes) {slots : List (Fin 2)}
    (path : Path slots) (current : Digest) :
    walk nodes slots (foldPath hash path current) = some current ∨
      CrossTraceCollision hash (nodeInputs nodes) (inputTrace hash path current) ∨
      MissingHit hash nodes (foldPath hash path current) (inputTrace hash path current) := by
  classical
  by_cases hc : CrossTraceCollision hash (nodeInputs nodes) (inputTrace hash path current)
  · exact Or.inr (Or.inl hc)
  by_cases hm : MissingHit hash nodes (foldPath hash path current) (inputTrace hash path current)
  · exact Or.inr (Or.inr hm)
  apply Or.inl
  apply walk_reconstruct hash nodes hconsistent path current _ hm
  intro left hl right hr heq
  by_contra hne
  exact hc ⟨left, hl, right, hr, hne, heq⟩


#print axioms walk_reconstruct
#print axioms recover_or_bad

end AspisR1.BinMerkleRecovery
