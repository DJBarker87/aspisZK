import R1Z.PV_RunJoin_PublicSamplerByteStep54
import R1Z.PV_RunJoin_SamplerByteLoop54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_PublicSamplerByteLoop54

theorem complete (n : Nat) (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize)
    (hi : i.val+n=8) :
    AspisR1PublicPreparation.sampler.qm31_digits_loop0 block rank i=
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0 block rank i := by
  induction n generalizing rank i with
  | zero =>
    have stop : ¬ i<8#usize := by change ¬ i.val<8;omega
    unfold AspisR1PublicPreparation.sampler.qm31_digits_loop0
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0
    rw [loop,loop]
    simp only [AspisR1PublicPreparation.sampler.qm31_digits_loop0.body,
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0.body,if_neg stop]
  | succ n ih =>
    have small : i.val<8 := by omega
    obtain ⟨next,hraw⟩ := PV_RunJoin_SamplerByteStep54.complete block rank i small
    have hactual := (PV_RunJoin_PublicSamplerByteStep54.complete block rank i small).trans hraw
    have inc := PV_RunJoin_SamplerCounters54.increment i (by omega)
    have tail := ih next (Usize.wrapping_add i 1#usize) (by omega)
    unfold AspisR1PublicPreparation.sampler.qm31_digits_loop0
      PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_digits_loop0
    rw [loop,loop]
    simp only [hactual,hraw]
    exact tail
#print axioms complete
end R1Z.PV_RunJoin_PublicSamplerByteLoop54
