import R1Z.PV_RunJoin_PartsTail19
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PartsTotal19
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderStdModels BuilderRecordsFields
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments

theorem source (w : RW) (p : RP) (hw : WitnessOk (wordWitness w)) :
    ∃ pt, parts w p = ok pt := by
  let f := parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256
  let g := blockR (wordWitness w) (wordPublic p)
  have hf : ∀ i : Usize, i.val < 57 → f.call_mut (w,p) i = ok (g i.val,(w,p)) := by
    intro i hi
    change parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256.call_mut (w,p) i = _
    rw [parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256.call_mut,
      PV_Src_Forest_BlockResult.writer_ok w p i hi]
    rfl
  obtain ⟨blocks,hblocks,_⟩ := PV_Src_Forest_BlockCollect.vector_values f g (w,p) hf
  obtain ⟨path,hpath⟩ := PV_RunJoin_PartsTail19.path_total w p
  obtain ⟨aux,haux⟩ := PV_RunJoin_PartsTail19.aux_total w p hw
  rw [parts]
  simp only [BuilderForestStdPort.core.iter.traits.iterator.Iterator.map.default,iterMap,bind_tc_ok]
  change ∃ pt, (do
    let blocks ← core.iter.traits.iterator.Iterator.collect.default (PV_Src_Forest_BankCollect.mapped f)
      (core.iter.traits.collect.FromIteratorVec (Array U32 256#usize)) ⟨⟨0#usize,57#usize⟩,(w,p)⟩
    _) = ok pt
  rw [hblocks]
  simp only [bind_tc_ok]
  rw [PV_Src_Forest_PathContent.arrays]
  simp only [bind_tc_ok,PV_Src_Forest_PrimitiveWriters.write_path_block]
  change ∃ pt, (do let b ← pathR (wordWitness w) (wordPublic p); _) = ok pt
  rw [hpath]
  simp only [bind_tc_ok]
  have he := congrArg (fun body : Result (Array U32 256#usize) => do
      let a ← body
      ok ({blocks := blocks,path := path,aux := a} : Parts))
    (PV_Src_Forest_AuxContent.aux_callee w p)
  simp only [bind_assoc_eq] at he
  rw [he,haux]
  exact ⟨_,rfl⟩
#print axioms source

theorem transfer : ∃ pt, parts PV_RunJoin_ReferenceFixtureResults.transferWitness
    PV_RunJoin_ReferenceFixtureResults.transferPublic = ok pt :=
  source _ _ PV_RunJoin_ReferenceFixtureResults.transfer_checked
#print axioms transfer

theorem withdrawal : ∃ pt, parts PV_RunJoin_ReferenceFixtureResults.withdrawalWitness
    PV_RunJoin_ReferenceFixtureResults.withdrawalPublic = ok pt :=
  source _ _ PV_RunJoin_ReferenceFixtureResults.withdrawal_checked
#print axioms withdrawal
end R1Z.PV_RunJoin_PartsTotal19
