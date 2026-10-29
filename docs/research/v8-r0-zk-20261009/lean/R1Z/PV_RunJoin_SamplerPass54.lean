import R1Z.PV_RunJoin_SamplerDivLoop54
import R1Z.PV_RunJoin_CircleNeutralCast53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerPass54
open PV_RunJoin_CircleRawSampler52 PV_RunJoin_CircleNeutralShape53

theorem complete (rank : Array U32 8#usize) :
    ∃ next digit, shipped_sampler.qm31_div_pass rank=ok (next,digit) ∧ Canon digit := by
  obtain ⟨next,rem,hr,hrem⟩ := PV_RunJoin_SamplerDivLoop54.complete 8 rank 0#u64 8#usize rfl (by omega) (by decide)
  refine ⟨next,UScalar.cast .U32 rem,?_,?_⟩
  · unfold shipped_sampler.qm31_div_pass
    rw [hr,bind_tc_ok]
    rfl
  · unfold Canon
    rw [PV_RunJoin_CircleNeutralCast53.down_val rem (by omega)]
    exact hrem
#print axioms complete
end R1Z.PV_RunJoin_SamplerPass54
