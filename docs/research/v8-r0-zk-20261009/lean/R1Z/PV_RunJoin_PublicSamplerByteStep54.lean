import R1Z.PV_RunJoin_PublicSamplerDiv54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_PublicSamplerByteStep54

theorem complete (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) (hi : i.val<8) :
    AspisR1PublicPreparation.sampler.qm31_digits_loop0.body block rank i=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0.body block rank i := by
  have go : i<8#usize := hi
  have hstart : (Usize.wrapping_mul 4#usize i).val<32 := by
    rw [PV_RunJoin_SamplerByteIndices54.mul4 i hi];omega
  unfold AspisR1PublicPreparation.sampler.qm31_digits_loop0.body
    PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0.body
  simp only [if_pos go,PV_RunJoin_SamplerChecked54.mul4 i hi,lift,bind_tc_ok,
    PV_RunJoin_SamplerChecked54.add _ 1#usize hstart (by decide),
    PV_RunJoin_SamplerChecked54.add _ 2#usize hstart (by decide),
    PV_RunJoin_SamplerChecked54.add _ 3#usize hstart (by decide),
    PV_RunJoin_SamplerChecked54.add i 1#usize (by omega) (by decide)]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_PublicSamplerByteStep54
