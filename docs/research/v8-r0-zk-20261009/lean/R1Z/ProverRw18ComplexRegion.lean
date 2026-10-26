import R1Z.ProverRw18ComplexBytes
set_option autoImplicit false
namespace R1Z.ProverRw18ComplexRegion
open Aeneas Aeneas.Std Result ProverRw18ComplexWrite

def write (x : C) (out : Slice U8) (start stop : Usize) : Result (Slice U8) := do
  let (segment,back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) out ⟨start,stop⟩
  let result ← source x segment
  ok (back result)

def output (x : C) (out : Slice U8) (start : Usize) : Slice U8 :=
  ⟨out.val.setSlice! start.val (ProverRw18ComplexBytes.bytes x),by
    simp only [List.length_setSlice!];exact out.property⟩

theorem exact_write (x : C) (out : Slice U8) (start stop : Usize)
    (ordered : start.val≤stop.val) (bound : stop.val≤out.val.length)
    (size : stop.val-start.val=8) : write x out start stop=ok (output x out start) := by
  have inside : start≤stop ∧ stop.val≤out.length := ⟨ordered,bound⟩
  let segment : Slice U8 := ⟨out.val.slice start.val stop.val,
    (out.val.slice_length_le start.val stop.val).trans out.property⟩
  have length : segment.val.length=8 := by
    simp only [segment,List.slice,List.length_take,List.length_drop]
    omega
  unfold write core.slice.index.Slice.index_mut core.slice.index.SliceIndexRangeUsizeSlice
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut
  simp only [inside,if_true,bind_tc_ok,Aeneas.Std.uncurry]
  change (do
    let result ← source x segment
    ok (⟨out.val.setSlice! start.val result.val,_⟩ : Slice U8))=_
  rw [ProverRw18ComplexWrite.exact_write x segment (by omega)]
  simp only [bind_tc_ok]
  congr 1
  apply Subtype.ext
  change out.val.setSlice! start.val (ProverRw18ComplexWrite.output x segment).val=_
  rw [ProverRw18ComplexBytes.output_value x segment (by omega),
    List.drop_eq_nil_iff.mpr (by omega : segment.val.length≤8),List.append_nil]
  rfl

#print axioms exact_write
end R1Z.ProverRw18ComplexRegion
