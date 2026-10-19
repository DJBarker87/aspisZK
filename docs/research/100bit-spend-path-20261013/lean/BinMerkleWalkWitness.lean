import BinMerkleRecovery

/-! A successful finite-table walk induces a literal Merkle path whose
preimages are among the recorded node inputs. This is a deterministic
reconstruction fact only. -/
set_option autoImplicit false
namespace AspisR1.BinMerkleWalkWitness

open BinMerkle32Path BinMerkleTable BinMerkleRecovery

theorem walk_witness (hash : List Byte → Digest) (nodes : Nodes)
    (hcons : BinMerkleRecovery.Consistent hash nodes) :
    ∀ {slots : List (Fin 2)} (root leaf : Digest),
      BinMerkleTable.walk nodes slots root = some leaf →
      ∃ path : BinMerkle32Path.Path slots,
        BinMerkle32Path.foldPath hash path leaf = root ∧
        ∀ input ∈ BinMerkle32Path.inputTrace hash path leaf,
          input ∈ BinMerkleRecovery.nodeInputs nodes := by
  intro slots
  induction slots with
  | nil =>
      intro root leaf h
      simp [BinMerkleTable.walk] at h
      subst leaf
      refine ⟨.nil, ?_, ?_⟩
      · rfl
      · simp [BinMerkle32Path.inputTrace]
  | cons slot slots ih =>
      intro root leaf h
      cases hw : BinMerkleTable.walk nodes slots root with
      | none =>
          simp [BinMerkleTable.walk, hw] at h
      | some parent =>
          have hmap : (BinMerkleTable.lookup nodes parent).map (fun cs => cs slot) = some leaf := by
            simpa [BinMerkleTable.walk, hw] using h
          cases hl : BinMerkleTable.lookup nodes parent with
          | none =>
              simp [hl] at hmap
          | some cs =>
              have hvalue : cs slot = leaf := by
                simpa [hl] using hmap
              have hentry : (cs, parent) ∈ nodes := BinMerkleTable.lookup_mem hl
              obtain ⟨tailPath, htailFold, htailInputs⟩ := ih root parent hw
              have hfill : BinMerkle32Path.fillChild slot cs leaf = cs := by
                funext i
                by_cases hi : i = slot
                · subst i
                  simp [BinMerkle32Path.fillChild, hvalue]
                · simp [BinMerkle32Path.fillChild, hi]
              refine ⟨BinMerkle32Path.Path.cons (slot := slot) cs tailPath, ?_, ?_⟩
              · change BinMerkle32Path.foldPath hash tailPath
                  (hash (BinMerkle32Path.nodeInput
                    (BinMerkle32Path.fillChild slot cs leaf))) = root
                rw [hfill, hcons cs parent hentry]
                exact htailFold
              · have htrace : BinMerkle32Path.inputTrace hash
                    (BinMerkle32Path.Path.cons (slot := slot) cs tailPath) leaf =
                    BinMerkle32Path.nodeInput cs ::
                      BinMerkle32Path.inputTrace hash tailPath parent := by
                  simp [BinMerkle32Path.inputTrace, hfill, hcons cs parent hentry]
                intro input hin
                rw [htrace] at hin
                rcases List.mem_cons.mp hin with hhead | htail
                · subst input
                  apply List.mem_map.mpr
                  exact ⟨(cs, parent), hentry, rfl⟩
                · exact htailInputs input htail

#print axioms walk_witness

end AspisR1.BinMerkleWalkWitness
