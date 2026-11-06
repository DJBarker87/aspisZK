import NJU_FieldDecode
set_option autoImplicit false
noncomputable section
namespace NJU_FieldFailure
open Aeneas Aeneas.Std Result AspisR1

/-- Exact emitted field abort on any bad word in the selected bounded window.
This is the scalar/window law paired with the raw no-return native cuts. -/
theorem noncanonical (bytes : Slice U8) (i : Usize) (small : i.val<64) (j : Fin 8)
 (fits : 32*i.val+32≤bytes.val.length)
 (bad : 2147483647≤NIG_FinishInput.word bytes.val (32*i.val+4*j.val)) :
 AspisR1CurrentWide.Proof.finishField bytes i=fail .panic := by
 let b : Array U8 32#usize:=⟨(bytes.val.drop (32*i.val)).take 32,by
  simp only [List.length_take,List.length_drop];change _=32;omega⟩
 have range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  bytes {start:=NJU_FieldScalar.start i small,«end»:=NJU_FieldScalar.stop i small}=ok b.to_slice := by
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst]
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
  split
  · apply congrArg Result.ok
    apply Subtype.ext
    simp only [List.slice]
    change (bytes.val.drop (i.val*32)).take ((i.val+1)*32-i.val*32)=
     (bytes.val.drop (32*i.val)).take 32
    congr 2 <;> omega
  · rename_i outside
    exfalso
    apply outside
    constructor
    · change i.val*32≤(i.val+1)*32
      omega
    · change (i.val+1)*32≤bytes.val.length
      omega
 have localBad : 2147483647≤NIG_FinishInput.word b.val (4*j.val) := by
  change 2147483647≤NIG_FinishInput.word ((bytes.val.drop (32*i.val)).take 32) (4*j.val)
  rw [NJR_FinishWindows.word_window _ (32*i.val) 32 (4*j.val) (by omega)]
  exact bad
 have decoded:=NJU_FieldDecode.none_of_bad b j localBad
 have actual:=NJU_FieldScalar.abort_none AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
  bytes b.to_slice i small range decoded
 unfold AspisR1CurrentWide.Proof.finishField
 rw [actual]
 rfl

theorem short (bytes : Slice U8) (i : Usize) (small : i.val<64)
 (bad : bytes.val.length<32*i.val+32) :
 AspisR1CurrentWide.Proof.finishField bytes i=fail .panic := by
 have actual:=NJU_FieldScalar.abort_short AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i small bad
 unfold AspisR1CurrentWide.Proof.finishField
 rw [actual]
 rfl

theorem primitive_noncanonical (bytes : Slice U8) (i : Usize) (small : i.val<64) (j : Fin 8)
 (fits : 32*i.val+32≤bytes.val.length)
 (bad : 2147483647≤NIG_FinishInput.word bytes.val (32*i.val+4*j.val)) :
 FIn_Primitives.field bytes i=fail .panic := by
 unfold FIn_Primitives.field
 rw [noncanonical bytes i small j fits bad]
 rfl

#print axioms noncanonical
#print axioms short
#print axioms primitive_noncanonical
end NJU_FieldFailure
