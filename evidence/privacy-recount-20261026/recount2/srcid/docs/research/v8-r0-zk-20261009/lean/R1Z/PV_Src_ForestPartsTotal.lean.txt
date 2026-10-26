import R1Z.PV_Src_Forest_PartsComplete

/-! Totality of the actual extracted Parts computation, for arbitrary raw
records. No spend, range, canonicality or callee-success premise is used. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ForestPartsTotal
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_Src_Forest_PrimitiveArguments BuilderStdModels
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder

theorem path_total (bits : Array U32 24#usize)
    (cur l r : Array (Array U32 8#usize) 24#usize) :
    ∃ out, R0WriterCopies.write_path_block bits cur l r = ok out := by
  obtain ⟨out,ho,_⟩ := path_block_loop bits cur l r 24 0#usize
    (Array.repeat 1536#usize 0#u32) (by simp)
  exact ⟨out,ho⟩

theorem sub_total (a b : U32) : ∃ z, R0WriterCopies.m31_sub a b = ok z := by
  rw [R0WriterCopies.m31_sub]
  simp only [lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem value_total (values : Array U32 3#usize) :
    ∃ out, R0WriterCopies.write_value_block values = ok out := by
  obtain ⟨v,hv,_⟩ := value_outer values 3 0#usize (Array.repeat 256#usize 0#u32) (by simp)
  obtain ⟨z,hz⟩ := sub_total values.val[0]! values.val[1]!
  have e96 : (Usize.wrapping_mul 6#usize 16#usize).val = 96 := by rw [umul _ _ (by simp)]; simp
  have e97 : (Usize.wrapping_add (Usize.wrapping_mul 6#usize 16#usize) 1#usize).val = 97 := by
    rw [uadd _ _ (by rw [e96]; simp),e96]; simp
  have e98 : (Usize.wrapping_add (Usize.wrapping_mul 6#usize 16#usize) 2#usize).val = 98 := by
    rw [uadd _ _ (by rw [e96]; simp),e96]; simp
  have e112 : (Usize.wrapping_mul 7#usize 16#usize).val = 112 := by rw [umul _ _ (by simp)]; simp
  have e113 : (Usize.wrapping_add (Usize.wrapping_mul 7#usize 16#usize) 1#usize).val = 113 := by
    rw [uadd _ _ (by rw [e112]; simp),e112]; simp
  rw [R0WriterCopies.write_value_block,hv]
  simp only [lift,bind_tc_ok]
  rw [index_ok values 0#usize (by decide),index_ok values 1#usize (by decide)]
  simp only [bind_tc_ok]
  simp only [UScalar.ofNatCore_val_eq]
  rw [hz]
  simp only [bind_tc_ok]
  rw [update_ok _ _ _ (by rw [e96]; simp)]
  simp only [lift,bind_tc_ok]
  rw [update_ok _ _ _ (by rw [e97]; simp)]
  simp only [lift,bind_tc_ok]
  rw [update_ok _ _ _ (by rw [e98]; simp)]
  simp only [lift,bind_tc_ok]
  rw [update_ok _ _ _ (by rw [e112]; simp)]
  simp only [lift,bind_tc_ok]
  rw [index_ok values 2#usize (by decide)]
  simp only [lift,bind_tc_ok]
  rw [update_ok _ _ _ (by rw [e113]; simp)]
  exact ⟨_,rfl⟩

theorem aux_total (values : Array U32 3#usize) (input output : R0WriterCopies.OccRecord) :
    ∃ out, R0WriterCopies.write_aux_block values input output = ok out := by
  obtain ⟨v,hv⟩ := value_total values
  obtain ⟨i,hi,_⟩ := occ_row v 9#usize (by decide) input
  obtain ⟨o,ho,_⟩ := occ_row i 10#usize (by decide) output
  refine ⟨o,?_⟩
  rw [R0WriterCopies.write_aux_block,hv]
  simp only [bind_tc_ok]
  rw [hi]
  simp only [bind_tc_ok]
  exact ho

theorem parts_total (w : RW) (p : RP) : ∃ pt, parts w p = ok pt := by
  let f := parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256
  let g := blockR (wordWitness w) (wordPublic p)
  have hf : ∀ i : Usize, i.val < 57 → f.call_mut (w,p) i = ok (g i.val,(w,p)) := by
    intro i hi
    change parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256.call_mut (w,p) i = _
    rw [parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256.call_mut,
      PV_Src_Forest_BlockResult.writer_ok w p i hi]
    rfl
  obtain ⟨blocks,hblocks,_⟩ := PV_Src_Forest_BlockCollect.vector_values f g (w,p) hf
  obtain ⟨path,hpath⟩ := path_total w.bits (curArr (wordWitness w) (wordPublic p))
    (leftArr (wordWitness w) (wordPublic p)) (rightArr (wordWitness w) (wordPublic p))
  obtain ⟨output,houtput,_⟩ := PV_Src_Forest_AuxContent.output_record w p
  obtain ⟨aux,haux⟩ := aux_total
    (Array.make 3#usize [w.input_value,w.output_value,w.change_value])
    (PV_Src_Forest_PrimitiveWriters.occRecord (inputRecord w)) (PV_Src_Forest_PrimitiveWriters.occRecord output)
  refine ⟨⟨blocks,path,aux⟩,?_⟩
  unfold parts
  simp only [BuilderForestStdPort.core.iter.traits.iterator.Iterator.map.default,iterMap,bind_tc_ok]
  change (do let blocks ← core.iter.traits.iterator.Iterator.collect.default (PV_Src_Forest_BankCollect.mapped f)
                (core.iter.traits.collect.FromIteratorVec (Array U32 256#usize)) ⟨⟨0#usize,57#usize⟩,(w,p)⟩
             _) = _
  rw [hblocks]
  simp only [bind_tc_ok]
  rw [PV_Src_Forest_PathContent.arrays]
  simp only [bind_tc_ok,PV_Src_Forest_PrimitiveWriters.write_path_block,hpath]
  rw [in_record,houtput]
  simp only [bind_tc_ok,PV_Src_Forest_PrimitiveWriters.write_aux_block,haux]

#print axioms path_total
#print axioms sub_total
#print axioms value_total
#print axioms aux_total
#print axioms parts_total
end R1Z.PV_Src_ForestPartsTotal
