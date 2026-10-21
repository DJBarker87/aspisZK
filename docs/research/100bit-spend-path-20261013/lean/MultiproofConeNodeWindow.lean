import MultiproofConeRead32
import MultiproofConeSlices

set_option autoImplicit false
namespace AspisR1.MultiproofConeNodeWindow
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeSlices

/-- Exactly the physical sibling window, including its short rejection case.
There is no bound on the physical slice length beyond the Slice type. -/
def window (physical : Slice U8) (cursor : Usize) : Slice U8 :=
  ⟨(physical.val.drop cursor.val).take 32,by
    have hb := physical.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem window_length (physical : Slice U8) (cursor : Usize) :
    (window physical cursor).val.length=min 32 (physical.val.length-cursor.val) := by
  simp only [window,List.length_take,List.length_drop]

theorem short_iff (physical : Slice U8) (cursor : Usize) :
    (window physical cursor).val.length < 32 ↔ physical.val.length-cursor.val < 32 := by
  rw [window_length];omega

/-- Checked range/reader composition: all 32 bytes come from the original
physical slice. It proves the window content law independently of Kani's
arbitrary-window transition gates. -/
theorem physical_read (physical : Slice U8) (cursor : Usize)
    (enough : cursor.val+32 ≤ physical.val.length) :
    ∃ finish chunk view,
      cursor+32#usize=ok finish ∧ finish.val=cursor.val+32 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        physical {start:=cursor,«end»:=finish}=ok view ∧
      reference.read32 view=ok chunk ∧ chunk.val=(window physical cursor).val := by
  have capacity := physical.property
  obtain ⟨finish,eqfinish,finishVal⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=cursor) (y:=32#usize) (by scalar_tac))
  have val : finish.val=cursor.val+32 := by scalar_tac
  have rangeEq := range_total physical cursor finish (by omega) (by omega)
  have len : (sub physical cursor finish).val.length=32 := by
    rw [sub_length physical cursor finish (by omega) (by omega),val]
    omega
  obtain ⟨chunk,eqchunk,chunkVal⟩ := MultiproofConeRead32.read32_total
    (sub physical cursor finish) (by omega)
  refine ⟨finish,chunk,sub physical cursor finish,eqfinish,val,rangeEq,eqchunk,?_⟩
  rw [chunkVal,List.take_of_length_le (by omega)]
  simp only [sub,window,val,Nat.add_sub_cancel_left]

#print axioms window_length
#print axioms short_iff
#print axioms physical_read
end AspisR1.MultiproofConeNodeWindow
