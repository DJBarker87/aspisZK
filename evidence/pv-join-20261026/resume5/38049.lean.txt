import R1Z.PV_Join_ArithmeticCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_ScaleCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ArithmeticCanonical5

def scale (x : aspis_core.field.QM31) (s : U32) :=
  ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ
    (AspisR1ProducerRelease47.field.QM31.mul_m31 (ProverRwDictionaryTower.toQ x) s)

theorem canonical (x : aspis_core.field.QM31) (s : U32) :
    ∃ z, scale x s = .ok z ∧ Q z := by
  obtain ⟨z,hz,hc,_⟩ := ProverRw18FieldMeaning.scale (old x) s
  rw [full_old] at hz
  exact ⟨_,hz,full_canonical z hc⟩

#print axioms canonical
end R1Z.PV_Join_ScaleCanonical5
