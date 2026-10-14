import R1MerkleRecovery

/-! A successful finite-table walk induces a literal Merkle path whose
preimages are among the recorded node inputs. This is a deterministic
reconstruction fact only. -/
set_option autoImplicit false
namespace AspisR1.MerkleWalkWitness

open Merkle32Path MerkleTable MerkleRecovery

theorem walk_witness (hash : List Byte → Digest) (nodes : Nodes)
    (hcons : MerkleRecovery.Consistent hash nodes) :
    ∀ {slots : List (Fin 8)} (root leaf : Digest),
      MerkleTable.walk nodes slots root = some leaf →
      ∃ path : Merkle32Path.Path slots,
        Merkle32Path.foldPath hash path leaf = root ∧
        ∀ input ∈ Merkle32Path.inputTrace hash path leaf,
          input ∈ MerkleRecovery.nodeInputs nodes := by
  intro slots
  induction slots with
  | nil =>
      intro root leaf h
      simp [MerkleTable.walk] at h
      subst leaf
      refine ⟨.nil, ?_, ?_⟩
      · rfl
      · simp [Merkle32Path.inputTrace]
  | cons slot slots ih =>
      intro root leaf h
      cases hw : MerkleTable.walk nodes slots root with
      | none =>
          simp [MerkleTable.walk, hw] at h
      | some parent =>
          have hmap : (MerkleTable.lookup nodes parent).map (fun cs => cs slot) = some leaf := by
            simpa [MerkleTable.walk, hw] using h
          cases hl : MerkleTable.lookup nodes parent with
          | none =>
              simp [hl] at hmap
          | some cs =>
              have hvalue : cs slot = leaf := by
                simpa [hl] using hmap
              have hentry : (cs, parent) ∈ nodes := MerkleTable.lookup_mem hl
              obtain ⟨tailPath, htailFold, htailInputs⟩ := ih root parent hw
              have hfill : Merkle32Path.fillChild slot cs leaf = cs := by
                funext i
                by_cases hi : i = slot
                · subst i
                  simp [Merkle32Path.fillChild, hvalue]
                · simp [Merkle32Path.fillChild, hi]
              refine ⟨.cons cs tailPath, ?_, ?_⟩
              · change Merkle32Path.foldPath hash tailPath
                  (hash (Merkle32Path.nodeInput
                    (Merkle32Path.fillChild slot cs leaf))) = root
                rw [hfill, hcons cs parent hentry]
                exact htailFold
              · have htrace : Merkle32Path.inputTrace hash (.cons cs tailPath) leaf =
                    Merkle32Path.nodeInput cs ::
                      Merkle32Path.inputTrace hash tailPath parent := by
                  simp [Merkle32Path.inputTrace, hfill, hcons cs parent hentry]
                intro input hin
                rw [htrace] at hin
                rcases List.mem_cons.mp hin with hhead | htail
                · subst input
                  apply List.mem_map.mpr
                  exact ⟨(cs, parent), hentry, rfl⟩
                · exact htailInputs input htail

#print axioms walk_witness

end AspisR1.MerkleWalkWitness
