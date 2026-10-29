import R1Z.PV_RunJoin_SamplerDigitStep54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerDigitLoop54
open PV_RunJoin_CircleRawSampler52 PV_RunJoin_SamplerPrefix54

theorem complete (n : Nat) (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize)
    (hi : i.val+n=4) (hp : Prefix i.val digits) :
    ∃ next, shipped_sampler.qm31_digits_loop1 rank digits i=ok next ∧ Prefix 4 next := by
  induction n generalizing rank digits i with
  | zero =>
    have stop : ¬ i<4#usize := by change ¬ i.val<4;omega
    refine ⟨digits,?_,?_⟩
    · unfold shipped_sampler.qm31_digits_loop1
      rw [loop]
      simp only [shipped_sampler.qm31_digits_loop1.body,if_neg stop]
    · have same : i.val=4 := by omega
      simpa only [same] using hp
  | succ n ih =>
    have small : i.val<4 := by omega
    obtain ⟨next,updated,hstep,hprefix⟩ := PV_RunJoin_SamplerDigitStep54.complete rank digits i small hp
    have inc := PV_RunJoin_SamplerCounters54.increment i (by omega)
    obtain ⟨last,htail,hlast⟩ := ih next updated (Usize.wrapping_add i 1#usize) (by omega)
      (by simpa only [inc] using hprefix)
    refine ⟨last,?_,hlast⟩
    unfold shipped_sampler.qm31_digits_loop1
    rw [loop]
    simp only [hstep]
    exact htail
#print axioms complete
end R1Z.PV_RunJoin_SamplerDigitLoop54
