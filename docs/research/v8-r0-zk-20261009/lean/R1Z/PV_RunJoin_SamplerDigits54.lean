import R1Z.PV_RunJoin_SamplerByteLoop54
import R1Z.PV_RunJoin_SamplerDigitLoop54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerDigits54
open PV_RunJoin_CircleRawSampler52 PV_RunJoin_SamplerPrefix54

theorem complete (block : Array U8 32#usize) :
    ∃ digits, shipped_sampler.qm31_digits block=ok digits ∧ Prefix 4 digits := by
  obtain ⟨rank,hrank⟩ := PV_RunJoin_SamplerByteLoop54.complete 8 block (Array.repeat 8#usize 0#u32) 0#usize rfl
  obtain ⟨digits,hdigits,hprefix⟩ := PV_RunJoin_SamplerDigitLoop54.complete 4 rank
    (Array.repeat 4#usize 0#u32) 0#usize rfl (zero _)
  exact ⟨digits,by simp only [shipped_sampler.qm31_digits,hrank,bind_tc_ok,hdigits],hprefix⟩
#print axioms complete
end R1Z.PV_RunJoin_SamplerDigits54
