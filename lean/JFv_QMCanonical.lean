import JFv_CanonicalSlice
set_option autoImplicit false
namespace AspisR1.JFv_QMCanonical
open Aeneas Aeneas.Std Result WP
open OraclePortCompactDraft MultiproofConeCanonical
open AspisR1DecodeKFullV10

theorem success (input : Slice U8) (length : input.length=16)
    (canon : canonical (bytesOf input.val)) :
    ∃ value, aspis_core.field.QM31.from_le_bytes input=ok (some value) := by
  let arr : Array U8 16#usize := ⟨input.val,length⟩
  have same : Array.to_slice arr=input := by cases input;rfl
  exact ⟨JFv_QM31.value arr,by rw [←same];exact JFv_QM31.success arr (JFv_CanonicalSlice.bounds arr canon)⟩

@[step] theorem spec (input : Slice U8) (length : input.length=16)
    (canon : canonical (bytesOf input.val)) :
    aspis_core.field.QM31.from_le_bytes input ⦃ result => ∃ value,result=some value ⦄ := by
  obtain ⟨value,call⟩ := success input length canon
  rw [call]
  exact ⟨value,rfl⟩

#print axioms success
#print axioms spec
end AspisR1.JFv_QMCanonical
