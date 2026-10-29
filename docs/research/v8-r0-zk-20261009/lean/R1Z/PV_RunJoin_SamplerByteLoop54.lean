import R1Z.PV_RunJoin_SamplerByteStep54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerByteLoop54
open PV_RunJoin_CircleRawSampler52

theorem complete (n : Nat) (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize)
    (hi : i.val+n=8) : ∃ next, shipped_sampler.qm31_digits_loop0 block rank i=ok next := by
  induction n generalizing rank i with
  | zero =>
    have stop : ¬ i<8#usize := by change ¬ i.val<8;omega
    refine ⟨rank,?_⟩
    unfold shipped_sampler.qm31_digits_loop0
    rw [loop]
    simp only [shipped_sampler.qm31_digits_loop0.body,if_neg stop]
  | succ n ih =>
    have small : i.val<8 := by omega
    obtain ⟨next,hstep⟩ := PV_RunJoin_SamplerByteStep54.complete block rank i small
    have inc : (Usize.wrapping_add i 1#usize).val+n=8 := by
      rw [PV_RunJoin_SamplerCounters54.increment i (by omega)];omega
    obtain ⟨last,htail⟩ := ih next _ inc
    refine ⟨last,?_⟩
    unfold shipped_sampler.qm31_digits_loop0
    rw [loop]
    simp only [hstep]
    exact htail
#print axioms complete
end R1Z.PV_RunJoin_SamplerByteLoop54
