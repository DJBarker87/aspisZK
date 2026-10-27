import R1Z.PV_CB_CanonicalQuartic
import R1Z.ProverCommitNativeQSquare49
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalQuarticMore
open Aeneas Aeneas.Std Result PV_CB_CanonicalTower

theorem square (a : Q) (ha : Valid a) :
    ∃ value, PV_CB_CurrentQuartic.S.square a = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,hcanonical,_⟩ := ProverCommitNativeQSquare49.square (old a) ha
  refine ⟨current value,?_,valid_current value hcanonical⟩
  rw [PV_CB_CurrentQuartic.square,source,hvalue]
  rfl

theorem scale (a : Q) (b : U32) :
    ∃ value, PV_CB_CurrentQuartic.S.scale a b = ok value ∧ Valid value := by
  let value := ProverCommitScalar48.product (old a) b
  refine ⟨current value,?_,valid_current value (ProverCommitScalar48.product_canonical _ _)⟩
  rw [PV_CB_CurrentQuartic.scale,source]
  have h := (ProverCommitScalar48.source_exact (old a) b).1
  have scale_eq (x : ProverRwDictionaryTower.NQ) :
      AspisR1ProducerRelease47.field.QM31.mul_m31 x b =
      AspisR1ProducerRelease47.scalar_ref x b := by
    simp only [AspisR1ProducerRelease47.field.QM31.mul_m31,
      AspisR1ProducerRelease47.field.CM31.mul_m31,
      AspisR1ProducerRelease47.scalar_ref,bind_assoc_eq,bind_tc_ok]
  rw [scale_eq,h]
  rfl
#print axioms square
#print axioms scale
end R1Z.PV_CB_CanonicalQuarticMore
