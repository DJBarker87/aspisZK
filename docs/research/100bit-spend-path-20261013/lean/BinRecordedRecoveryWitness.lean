import BinMerkleWalkWitness
import BinMerkleRecordedLog
import BinMerkleLogRecovery

/-! Invert a successful recorded-log recovery into the corresponding salted
leaf widths, a Merkle path, and membership of every opened preimage in the log. -/
set_option autoImplicit false
namespace AspisR1.BinRecordedRecoveryWitness

open BinMerkle32Path BinMerkle32Leaf BinMerkleTable BinMerkleLeafRecovery
open BinMerkleRecordedLog BinMerkleRecovery

theorem recover_witness (hash : List BinMerkle32Path.Byte → Digest) (log : Log)
    (hcons : BinMerkleRecordedLog.Consistent hash log)
    (tag : BinMerkle32Path.Byte) (width : Nat) (slots : List (Fin 2)) (root : Digest)
    (packed salt : List BinMerkle32Path.Byte)
    (hrec : BinMerkleLeafRecovery.recover (BinMerkleRecordedLog.nodes log)
      (BinMerkleRecordedLog.leaves tag width log) slots root = some (packed, salt)) :
    packed.length = width ∧ salt.length = 32 ∧
      ∃ path : Path slots,
        foldPath hash path (hash (leafInput tag packed salt)) = root ∧
        ∀ input ∈ fullTrace hash path (leafInput tag packed salt),
          input ∈ log.map Prod.fst := by
  unfold BinMerkleLeafRecovery.recover at hrec
  cases hwalk : BinMerkleTable.walk (BinMerkleRecordedLog.nodes log) slots root with
  | none => simp [hwalk] at hrec
  | some digest =>
      have hlookup :
          BinMerkleLeafRecovery.lookupLeaf (BinMerkleRecordedLog.leaves tag width log) digest =
            some (packed, salt) := by
        simpa [hwalk] using hrec
      have hleafMem := BinMerkleLeafRecovery.lookupLeaf_mem hlookup
      obtain ⟨recordedInput, hlogInput, hparse⟩ :=
        (BinMerkleRecordedLog.mem_leaves).mp hleafMem
      rcases BinMerkleLeafCodec.parse_sound tag width recordedInput (packed, salt) hparse with
        ⟨hwidth, hsalt, hinput⟩
      have hhash : hash (leafInput tag packed salt) = digest := by
        rw [hinput]
        exact hcons recordedInput digest hlogInput
      obtain ⟨path, hfold, hinputs⟩ :=
        BinMerkleWalkWitness.walk_witness hash (BinMerkleRecordedLog.nodes log)
          (BinMerkleRecordedLog.nodes_consistent hash log hcons) root digest hwalk
      rw [← hhash] at hfold
      have hpWidth : packed.length = width := by simpa using hwidth
      have hsWidth : salt.length = 32 := by simpa using hsalt
      refine ⟨hpWidth, hsWidth, path, hfold, ?_⟩
      intro input hin
      change input ∈ leafInput tag packed salt ::
        inputTrace hash path (hash (leafInput tag packed salt)) at hin
      rcases List.mem_cons.mp hin with hleaf | hnode
      · subst input
        exact List.mem_map.mpr ⟨(recordedInput, digest), hlogInput, hinput.symm⟩
      · rw [hhash] at hnode
        exact BinMerkleLogRecovery.nodeInputs_subset log (hinputs input hnode)


#print axioms recover_witness
end AspisR1.BinRecordedRecoveryWitness
