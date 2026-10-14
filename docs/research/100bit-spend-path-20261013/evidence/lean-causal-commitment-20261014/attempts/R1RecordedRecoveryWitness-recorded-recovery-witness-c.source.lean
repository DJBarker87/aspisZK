import R1MerkleWalkWitness
import R1MerkleRecordedLog

/-! Invert a successful recorded-log recovery into the corresponding salted
leaf widths, a Merkle path, and membership of every opened preimage in the log. -/
set_option autoImplicit false
namespace AspisR1.RecordedRecoveryWitness

open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery
open MerkleRecordedLog MerkleRecovery

theorem recover_witness (hash : List Merkle32Path.Byte → Digest) (log : Log)
    (hcons : MerkleRecordedLog.Consistent hash log)
    (tag : Merkle32Path.Byte) (width : Nat) (slots : List (Fin 8)) (root : Digest)
    (packed salt : List Merkle32Path.Byte)
    (hrec : MerkleLeafRecovery.recover (MerkleRecordedLog.nodes log)
      (MerkleRecordedLog.leaves tag width log) slots root = some (packed, salt)) :
    packed.length = width ∧ salt.length = 32 ∧
      ∃ path : Path slots,
        foldPath hash path (hash (leafInput tag packed salt)) = root ∧
        ∀ input ∈ fullTrace hash path (leafInput tag packed salt),
          input ∈ log.map Prod.fst := by
  unfold MerkleLeafRecovery.recover at hrec
  cases hwalk : MerkleTable.walk (MerkleRecordedLog.nodes log) slots root with
  | none => simp [hwalk] at hrec
  | some digest =>
      have hlookup :
          MerkleLeafRecovery.lookupLeaf (MerkleRecordedLog.leaves tag width log) digest =
            some (packed, salt) := by
        simpa [hwalk] using hrec
      have hleafMem := MerkleLeafRecovery.lookupLeaf_mem hlookup
      obtain ⟨recordedInput, hlogInput, hparse⟩ :=
        (MerkleRecordedLog.mem_leaves).mp hleafMem
      rcases MerkleLeafCodec.parse_sound tag width recordedInput (packed, salt) hparse with
        ⟨hwidth, hsalt, hinput⟩
      have hhash : hash (leafInput tag packed salt) = digest := by
        rw [hinput]
        exact hcons recordedInput digest hlogInput
      obtain ⟨path, hfold, hinputs⟩ :=
        MerkleWalkWitness.walk_witness hash (MerkleRecordedLog.nodes log)
          (MerkleRecordedLog.nodes_consistent hash log hcons) root digest hwalk
      rw [hhash] at hfold
      refine ⟨hwidth, hsalt, path, hfold, ?_⟩
      intro input hin
      change input ∈ leafInput tag packed salt ::
        inputTrace hash path (hash (leafInput tag packed salt)) at hin
      rcases List.mem_cons.mp hin with hleaf | hnode
      · subst input
        exact List.mem_map.mpr ⟨(recordedInput, digest), hlogInput, hinput.symm⟩
      · rw [hhash] at hnode
        exact MerkleLogRecovery.nodeInputs_subset log (hinputs input hnode)

#print axioms recover_witness

end AspisR1.RecordedRecoveryWitness
