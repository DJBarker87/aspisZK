import JFq_Range
import JFo_QueryRead
import JFn_FieldRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_ValueBlock
open Aeneas Aeneas.Std Result
open MultiproofConeSlices

def value (i : Fin 22) : Slice U8 :=
  ⟨((JFo_Opening.value i).val.drop 672).take 128,by
    have h:=(JFo_Opening.value i).property
    simp only [List.length_take,List.length_drop];omega⟩

theorem length (i : Fin 22) : (value i).val.length=128 := by
  simp only [value,List.length_take,List.length_drop,JFo_Opening.length]
  rfl

theorem selected (i : Fin 22) : (value i).val=
    (JFx_NativeBytes.proof.val.drop (10055+i.val*832+672)).take 128 := by
  rw [show (value i).val=((JFo_Opening.value i).val.drop 672).take 128 from rfl,
    JFo_Opening.selected,JFq_Range.nested _ _ 832 672 128 (by decide)]

theorem read (i : Fin 22) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (JFo_Opening.value i) {start:=672#usize,«end»:=800#usize}=ok (value i) := by
  have run := range_total (JFo_Opening.value i) 672#usize 800#usize (by decide)
    (by rw [JFo_Opening.length];decide)
  exact run

/-- The actual source decoder closure reads the final 128 bytes. It does
not call op21 on the beginning of the 832-byte opening. -/
theorem closure (seed : Port3_NativeQueryBody.Ops) (i : Fin 22) (j : Usize)
    (z : SAQ_WideABI.E) (decoded : SAQ_Decoder.read (value i) j=ok z) :
    Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (Port4C_RowStd.install (Port5Q1_QueryPorts.install (SAQ_Decoder.install seed)))
      (JFo_Opening.value i) j=ok (z,JFo_Opening.value i) := by
  simp only [Port3_NativeQueryBody.verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut,
    read,bind_tc_ok]
  exact congrArg (fun r => do let x ← r; ok (x,JFo_Opening.value i)) decoded

#print axioms length
#print axioms selected
#print axioms read
#print axioms closure
end AspisR1.JFn_ValueBlock
end
