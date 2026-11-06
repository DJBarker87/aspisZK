import NJU_FieldScalar
set_option autoImplicit false
noncomputable section
namespace NJU_FieldDecode
open Aeneas Aeneas.Std Result AspisR1
open ExtractedRecordByteCanonicality ExtractedRecordLimbCanonicality

/-- The actual emitted decoder is total on every 32-byte array, including
noncanonical words. No field value is supplied or assumed. -/
theorem total (b : Array U8 32#usize) :
 ∃ out, AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes b.to_slice=ok out := by
 rw [fixed_reads,wordArray8,from_limbs_make]
 exact ⟨_,rfl⟩

theorem word_value (b : Array U8 32#usize) (j : Fin 8) :
 (wordLE b j).val=NIG_FinishInput.word b.val (4*j.val) := by
 unfold wordLE
 rw [ExtractedRecordByteValue.from_le4_value]
 have size : b.val.length=32 := b.property
 have h0 : 4*j.val<b.val.length := by omega
 have h1 : 4*j.val+1<b.val.length := by omega
 have h2 : 4*j.val+2<b.val.length := by omega
 have h3 : 4*j.val+3<b.val.length := by omega
 simp only [NIG_FinishInput.word,byteAt,List.getElem?_eq_getElem h0,
  List.getElem?_eq_getElem h1,List.getElem?_eq_getElem h2,List.getElem?_eq_getElem h3,
  Option.getD_some]

/-- Universal actual None reply at any noncanonical word; paired with
NJU_K005/006 and the round/final window native cuts. -/
theorem none_of_bad (b : Array U8 32#usize) (j : Fin 8)
 (bad : 2147483647≤NIG_FinishInput.word b.val (4*j.val)) :
 AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes b.to_slice=ok none := by
 obtain ⟨out,run⟩:=total b
 cases out with
 | none => exact run
 | some value =>
  have canon:=((fixed_success_iff b value).mp run).1 j
  rw [word_value] at canon
  omega

theorem slice_none (bytes : Slice U8) (size : bytes.val.length=32) (j : Fin 8)
 (bad : 2147483647≤NIG_FinishInput.word bytes.val (4*j.val)) :
 AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes=ok none := by
 let b : Array U8 32#usize:=⟨bytes.val,size⟩
 have same : b.to_slice=bytes := by apply Subtype.ext; rfl
 rw [←same]
 exact none_of_bad b j bad

#print axioms total
#print axioms word_value
#print axioms none_of_bad
#print axioms slice_none
end NJU_FieldDecode
