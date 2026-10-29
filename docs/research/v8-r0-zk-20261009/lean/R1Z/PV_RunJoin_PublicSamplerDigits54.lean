import R1Z.PV_RunJoin_PublicSamplerByteLoop54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_PublicSamplerDigits54

theorem body (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize) :
    AspisR1PublicPreparation.sampler.qm31_digits_loop1.body rank digits i=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop1.body rank digits i := by
  unfold AspisR1PublicPreparation.sampler.qm31_digits_loop1.body
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop1.body
  by_cases go : i<4#usize
  · simp only [if_pos go,PV_RunJoin_PublicSamplerDiv54.complete,bind_tc_ok,
      PV_RunJoin_SamplerChecked54.add i 1#usize (by change i.val<32;have h : i.val<4 := go;omega) (by decide),lift]
  · simp only [if_neg go]

theorem loop (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize) :
    AspisR1PublicPreparation.sampler.qm31_digits_loop1 rank digits i=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop1 rank digits i := by
  unfold AspisR1PublicPreparation.sampler.qm31_digits_loop1
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop1
  simp only [body]

theorem complete (block : Array U8 32#usize) :
    AspisR1PublicPreparation.sampler.qm31_digits block=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits block := by
  unfold AspisR1PublicPreparation.sampler.qm31_digits
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits
  simp only [PV_RunJoin_PublicSamplerByteLoop54.complete,loop]
#print axioms body
#print axioms loop
#print axioms complete
end R1Z.PV_RunJoin_PublicSamplerDigits54
