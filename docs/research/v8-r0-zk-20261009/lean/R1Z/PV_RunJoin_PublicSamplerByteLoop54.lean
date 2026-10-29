import R1Z.PV_RunJoin_PublicSamplerByteStep54
import R1Z.PV_RunJoin_SamplerByteLoop54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_PublicSamplerByteLoop54

theorem body (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
    AspisR1PublicPreparation.sampler.qm31_digits_loop0.body block rank i=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0.body block rank i := by
  by_cases small : i<8#usize
  · exact PV_RunJoin_PublicSamplerByteStep54.complete block rank i small
  · unfold AspisR1PublicPreparation.sampler.qm31_digits_loop0.body
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0.body
    simp only [if_neg small]

theorem complete (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
    AspisR1PublicPreparation.sampler.qm31_digits_loop0 block rank i=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0 block rank i := by
  unfold AspisR1PublicPreparation.sampler.qm31_digits_loop0
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0
  simp only [body]
#print axioms body
#print axioms complete
end R1Z.PV_RunJoin_PublicSamplerByteLoop54
