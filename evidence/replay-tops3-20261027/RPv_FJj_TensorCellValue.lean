import RPv_FJj_TensorCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorCellValue
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)
open FJa_ReverseStep (Rev next)

def model (input : Slice NQ) (digit : Array NQ 4#usize) (j n : Usize) (t : Nat) :=
  if (FJj_TensorCell.index j n 3#usize).val=t then FJj_QMSlice.value input j.val*FJf_QMArray.value digit 3
  else if (FJj_TensorCell.index j n 2#usize).val=t then FJj_QMSlice.value input j.val*FJf_QMArray.value digit 2
  else if (FJj_TensorCell.index j n 1#usize).val=t then FJj_QMSlice.value input j.val*FJf_QMArray.value digit 1
  else if (FJj_TensorCell.index j n 0#usize).val=t then FJj_QMSlice.value input j.val*FJf_QMArray.value digit 0
  else FJj_QMSlice.value input t

theorem value (self : FIo_Native.weights.Weights) (k d n j : Usize)
    (row : Array (Array NQ 4#usize) 5#usize) (digit : Array NQ 4#usize)
    (hr : Array.index_usize self.factors k=ok row) (hd : Array.index_usize row d=ok digit)
    (iter cursor : Rev) (input out : Slice NQ)
    (hc : FJf_QMArray.canon digit) (hs : FJj_QMSlice.canon input)
    (hn : next iter=ok (some j,cursor))
    (run : FIo_Native.weights.Weights.tensor_loop0_loop0.body self k n d iter input=
      ok (.cont (cursor,out))) :
    FJj_QMSlice.canon out ∧ out.val.length=input.val.length ∧
      ∀ t,FJj_QMSlice.value out t=model input digit j n t := by
  obtain ⟨x,q0,q1,q2,q3,p0,p1,p2,p3,s0,s1,s2,hx,hq0,hp0,hs0,hq1,hp1,hs1,hq2,hp2,hs2,hq3,hp3,hs3⟩ :=
    FJj_TensorCell.source self k d n j row digit hr hd iter cursor input out hn run
  have cx := FJj_QMSlice.canonical_read input j x hs hx
  have cq0 := hc q0 (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hq0))
  have cq1 := hc q1 (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hq1))
  have cq2 := hc q2 (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hq2))
  have cq3 := hc q3 (List.mem_of_getElem? (FJc_ReadSlot.slot _ _ _ hq3))
  have v0 := FIo_QMMulValues.mul x q0 p0 cx cq0 hp0
  have v1 := FIo_QMMulValues.mul x q1 p1 cx cq1 hp1
  have v2 := FIo_QMMulValues.mul x q2 p2 cx cq2 hp2
  have v3 := FIo_QMMulValues.mul x q3 p3 cx cq3 hp3
  have c0 := FJj_QMSlice.update_canon input s0 _ p0 hs v0.1 hs0
  have c1 := FJj_QMSlice.update_canon s0 s1 _ p1 c0 v1.1 hs1
  have c2 := FJj_QMSlice.update_canon s1 s2 _ p2 c1 v2.1 hs2
  have c3 := FJj_QMSlice.update_canon s2 out _ p3 c2 v3.1 hs3
  refine ⟨c3,?_,?_⟩
  · exact (FJj_QMSliceUpdate.length _ _ _ _ hs3).trans
      ((FJj_QMSliceUpdate.length _ _ _ _ hs2).trans
        ((FJj_QMSliceUpdate.length _ _ _ _ hs1).trans (FJj_QMSliceUpdate.length _ _ _ _ hs0)))
  · intro t
    unfold model
    rw [FJj_QMSliceUpdate.value _ _ _ _ t hs3,FJj_QMSliceUpdate.value _ _ _ _ t hs2,
      FJj_QMSliceUpdate.value _ _ _ _ t hs1,FJj_QMSliceUpdate.value _ _ _ _ t hs0,
      v3.2,v2.2,v1.2,v0.2,←FJj_QMSlice.read input j x hx,
      ←FJf_QMArray.read digit 3#usize q3 hq3,←FJf_QMArray.read digit 2#usize q2 hq2,
      ←FJf_QMArray.read digit 1#usize q1 hq1,←FJf_QMArray.read digit 0#usize q0 hq0]
    rfl
#print axioms value
end AspisR1.FJj_TensorCellValue
end
