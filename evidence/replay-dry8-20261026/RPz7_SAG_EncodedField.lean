import RPz7_SAG_FieldRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_EncodedField
open Aeneas Aeneas.Std Result

theorem value {n : Nat} (fm : Slice U8) (f : Fin n → AspisWideTower.WideExact)
    (encoded : SelectedFieldSequenceCodec.encodeWide f = MultiproofConeCanonical.bytesOf fm.val)
    (index : Usize) (value : AspisR1CurrentWide.Proof.FinishE) (bound : index.val < n)
    (read : AspisR1CurrentWide.Proof.finishField fm index = ok value) :
    AspisR1CurrentWide.Proof.decodeFinish value = f ⟨index.val,bound⟩ := by
  have source := SAG_FieldRead.from_finish fm index value read
  have model := (SelectedFieldSequenceCodec.decodeWide_eq_some_iff
    (SelectedFieldSequenceCodec.encodeWide f) f).mp (SelectedFieldSequenceCodec.decodeWide_encode f)
  have point := model.2 ⟨index.val,bound⟩
  rw [encoded] at point
  exact Option.some.inj (source.symm.trans point)

#print axioms value
end AspisR1.SAG_EncodedField
end
