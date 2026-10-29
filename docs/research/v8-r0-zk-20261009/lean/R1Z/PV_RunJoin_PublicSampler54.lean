import R1Z.PV_RunJoin_PublicSamplerDigits54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_PublicSampler54
abbrev Q := (U32 × U32) × (U32 × U32)
def encode (q : Q) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
  ⟨⟨q.1.1,q.1.2⟩,⟨q.2.1,q.2.2⟩⟩

theorem complete (block : Array U8 32#usize) :
    AspisR1PublicPreparation.sampler.qm31_sample block=(do
      let q ← PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample block
      ok (encode q)) := by
  unfold AspisR1PublicPreparation.sampler.qm31_sample
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample
  simp only [PV_RunJoin_PublicSamplerDigits54.complete,
    AspisR1PublicPreparation.aspis_core.field.CM31.new,PV_RunJoin_CircleRawTower52.field.CM31.new,
    bind_assoc_eq,bind_tc_ok,encode]
#print axioms encode
#print axioms complete
end R1Z.PV_RunJoin_PublicSampler54
