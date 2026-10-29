import AspisR1PublicPreparation.Funs
import R1Z.PV_RunJoin_SamplerChecked54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_PublicSamplerDiv54

theorem body (rank : Array U32 8#usize) (rem : U64) (j : Usize) :
    AspisR1PublicPreparation.sampler.qm31_div_pass_loop.body rank rem j=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop.body rank rem j := by
  unfold AspisR1PublicPreparation.sampler.qm31_div_pass_loop.body
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop.body
  by_cases go : j>0#usize
  · simp only [if_pos go,PV_RunJoin_SamplerChecked54.sub_one j go,
      PV_RunJoin_SamplerChecked54.shift32,lift,bind_tc_ok]
    rfl
  · simp only [if_neg go]

theorem loop (rank : Array U32 8#usize) (rem : U64) (j : Usize) :
    AspisR1PublicPreparation.sampler.qm31_div_pass_loop rank rem j=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop rank rem j := by
  unfold AspisR1PublicPreparation.sampler.qm31_div_pass_loop
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass_loop
  simp only [body]

theorem complete (rank : Array U32 8#usize) :
    AspisR1PublicPreparation.sampler.qm31_div_pass rank=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass rank := by
  unfold AspisR1PublicPreparation.sampler.qm31_div_pass
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_div_pass
  simp only [loop]
#print axioms body
#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_PublicSamplerDiv54
