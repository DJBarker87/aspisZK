import R1Z.PV_RunJoin_SamplerDivStep54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerDivLoop54
open PV_RunJoin_CircleRawSampler52

theorem complete (n : Nat) (rank : Array U32 8#usize) (rem : U64) (j : Usize)
    (hj : j.val=n) (bound : n≤8) (hrem : rem.val<2147483647) :
    ∃ next r, shipped_sampler.qm31_div_pass_loop rank rem j=ok (next,r) ∧ r.val<2147483647 := by
  induction n generalizing rank rem j with
  | zero =>
    have stop : ¬ j>0#usize := by change ¬ 0<j.val;omega
    refine ⟨rank,rem,?_,hrem⟩
    unfold shipped_sampler.qm31_div_pass_loop
    rw [loop]
    simp only [shipped_sampler.qm31_div_pass_loop.body,if_neg stop,bind_tc_ok]
  | succ n ih =>
    obtain ⟨next,r,hstep,hr⟩ := PV_RunJoin_SamplerDivStep54.complete rank rem j (by omega) (by omega)
    have dec : (Usize.wrapping_sub j 1#usize).val=n := by
      rw [PV_RunJoin_SamplerCounters54.sub_one j (by omega)];omega
    obtain ⟨last,remain,htail,hremain⟩ := ih next r _ dec (by omega) hr
    refine ⟨last,remain,?_,hremain⟩
    unfold shipped_sampler.qm31_div_pass_loop
    rw [loop,hstep,bind_tc_ok]
    exact htail
#print axioms complete
end R1Z.PV_RunJoin_SamplerDivLoop54
