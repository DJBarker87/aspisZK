import JFn_ValueBlock
import FIp_DotsAdapter
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Windows
open Aeneas Aeneas.Std Result
open MultiproofConeSlices

def prefix608 (i : Fin 22) : Slice U8 :=
  ⟨(JFo_Opening.value i).val.take 608, by
    have h := (JFo_Opening.value i).property
    simp only [List.length_take]
    omega⟩

theorem length (i : Fin 22) : (prefix608 i).val.length=608 := by
  simp only [prefix608,List.length_take,JFo_Opening.length]
  rfl

def array (i : Fin 22) : Array U8 608#usize := ⟨(prefix608 i).val,length i⟩

theorem selected (i : Fin 22) (start count : Nat) (bound : start+count≤608) :
    (((array i).val.drop start).take count)=
      (JFx_NativeBytes.proof.val.drop (10055+i.val*832+start)).take count := by
  change (((JFo_Opening.value i).val.take 608).drop start).take count=_
  have nested := JFq_Range.nested (JFo_Opening.value i).val 0 608 start count bound
  simp only [List.drop_zero,Nat.zero_add] at nested
  rw [nested]
  simp only [List.drop_zero]
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 start count (by omega)]

/-- The native dot body selects exactly the first608 bytes, and the conversion
returns the same physical prefix608. Arithmetic remains a separate obligation. -/
theorem read (i : Fin 22) :
    (do
      let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        (JFo_Opening.value i) {«end»:=608#usize}
      let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError r)=ok (array i) := by
  have range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (JFo_Opening.value i) {«end»:=608#usize}=ok (prefix608 i) := by
    simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice,
      core.slice.index.SliceIndexRangeToUsize.get]
    exact (range_total (JFo_Opening.value i) 0#usize 608#usize (by decide)
      (by rw [JFo_Opening.length];decide))
  rw [range,bind_tc_ok]
  simp only [core.array.TryFromSharedArraySlice.try_from,length]
  rfl

#print axioms length
#print axioms selected
#print axioms read
end AspisR1.JFr_TX2_Windows
end
