import R1Z.PV_RunJoin_SamplerPrefix54
import R1Z.PV_RunJoin_SamplerCounters54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerDigitStep54
open PV_RunJoin_CircleRawSampler52 PV_RunJoin_SamplerPrefix54

theorem complete (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize)
    (hi : i.val<4) (hp : Prefix i.val digits) :
    ∃ next updated, shipped_sampler.qm31_digits_loop1.body rank digits i=
      ok (cont (next,updated,Usize.wrapping_add i 1#usize)) ∧ Prefix (i.val+1) updated := by
  obtain ⟨next,digit,hpass,hcanon⟩ := PV_RunJoin_SamplerPass54.complete rank
  obtain ⟨updated,hupdate,hprefix⟩ := update digits i digit hi hp hcanon
  refine ⟨next,updated,?_,hprefix⟩
  have go : i<4#usize := hi
  unfold shipped_sampler.qm31_digits_loop1.body
  simp only [if_pos go,hpass,bind_tc_ok,Aeneas.Std.uncurry,hupdate,lift]
#print axioms complete
end R1Z.PV_RunJoin_SamplerDigitStep54
