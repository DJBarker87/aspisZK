import R1Z.PV_Src_PathSiblings

/-! All private record fields of the transfer reference match the canonical
witness, with the membership index actually packed from its path bits. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_ReferenceTransfer
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort.pool_v1 PV_Src_CheckedEncoding

theorem witness (roots : BuilderRecordsReference.Roots) (w : W)
    (p : BuilderPublicProjection.Transfer)
    (s : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (anchor : Array U32 8#usize)
    (selected : (w.path 0).2 = if (w.path 0).1 then w.pair.firstCommitment else w.pair.secondCommitment) :
    PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_Src_RecordReference.returned roots
        (input w (transferRequest p w) (PV_Src_PathIndex.index w) s compiled anchor)).w =
      BuilderCanonical.rustWitness w := by
  rw [PV_Src_RecordReference.returned,PV_Src_RecordReference.word_witness]
  simp only [BuilderExtractedRecords.rawWitness,BuilderRecordsReference.witness,
    input,PV_Src_NativeInput.outputValue,PV_Src_NativeInput.recipient,transferRequest,
    PV_Src_RecordReference.note,recipient,change,Option.map_some,
    BuilderRecordsRecipient.owner,BuilderRecordsRecipient.salt,
    BuilderCanonical.rustWitness,BuilderSpendRelation.modelWitness,toRust]
  congr 1
  · exact PV_Src_PathBits.bits w
  · exact PV_Src_PathSiblings.siblings w _ selected

#print axioms witness
end R1Z.PV_Src_ReferenceTransfer
