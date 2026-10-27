import R1Z.PV_CB_CanonicalComplex
import R1Z.ProverRwDictionaryScalar
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CompressConstructors
open Aeneas Aeneas.Std Result ProverRwDictionaryTower
abbrev C := PV_CB_CanonicalComplex.C
abbrev Q := PV_CB_CanonicalTower.Q

def fromM31 (value : U32) : Result C := mapResult fromC
  (AspisR1ProducerRelease47.field.CM31.from_m31 value)
def fromCM31 (value : C) : Result Q := mapResult fromQ
  (AspisR1ProducerRelease47.field.QM31.from_cm31 (toC value))

theorem m31 (value : U32) : fromM31 value = ok ⟨value,0#u32⟩ := by
  simp only [fromM31,AspisR1ProducerRelease47.field.CM31.from_m31,
    AspisR1ProducerRelease47.field.M31.ZERO,mapResult,fromC]

theorem cm31 (value : C) : fromCM31 value = ok ⟨value,⟨0#u32,0#u32⟩⟩ := by
  simp only [fromCM31,AspisR1ProducerRelease47.field.QM31.from_cm31,
    AspisR1ProducerRelease47.field.CM31.ZERO,AspisR1ProducerRelease47.field.M31.ZERO,
    mapResult,toC,fromQ,fromC]

theorem m31_valid (value : U32) (valid : PV_CB_CanonicalM31.Valid value) :
    ∃ out, fromM31 value = ok out ∧ PV_CB_CanonicalComplex.Valid out :=
  ⟨⟨value,0#u32⟩,m31 value,⟨valid,by change (0#u32).val < AspisCircleGroupOrder.P;decide⟩⟩

theorem cm31_valid (value : C) (valid : PV_CB_CanonicalComplex.Valid value) :
    ∃ out, fromCM31 value = ok out ∧ PV_CB_CanonicalTower.Valid out :=
  ⟨⟨value,⟨0#u32,0#u32⟩⟩,cm31 value,⟨valid,⟨by change (0#u32).val < AspisCircleGroupOrder.P;decide,by change (0#u32).val < AspisCircleGroupOrder.P;decide⟩⟩⟩
#print axioms m31
#print axioms cm31
#print axioms m31_valid
#print axioms cm31_valid
end R1Z.PV_CB_CompressConstructors
