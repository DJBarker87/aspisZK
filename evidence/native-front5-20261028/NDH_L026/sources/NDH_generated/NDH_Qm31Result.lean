import NDH_Qm31Pass
import NDH_Cast
set_option autoImplicit false
namespace NDH_Qm31Result
open Aeneas Aeneas.Std Result
open AspisR1.SamplerMachineBounds AspisR1.SamplerWordPass
open AspisR1.ExtractedQM31SamplerPassLoop

theorem result (rank : Array U32 8#usize) :
    ∃ (out : Array U32 8#usize) (digit : U32),
      AspisR1Post25Sampler.sampler.qm31_div_pass rank = ok (out,digit) ∧
      digit.val = (machineProcess 0 (words rank).reverse).1.toNat ∧
      words out = (machineProcess 0 (words rank).reverse).2.reverse ∧
      digit.val < P := by
  obtain ⟨out,rem,run,remValue,outValue,remBound⟩ :=
    loop_correct rank 0#u64 8#usize (by decide) (by decide)
  rw [←NDH_Qm31Pass.loop_eq] at run
  have hr : rem.val < B := by
    have hp : P < B := by decide
    omega
  have castValue := NDH_Cast.cohort_cast rem hr
  have len := words_length rank
  have ht : (words rank).take 8 = words rank := by rw [←len, List.take_length]
  have hd : (words rank).drop 8 = [] := by rw [←len, List.drop_length]
  simp only [ht, hd, List.append_nil] at remValue outValue
  refine ⟨out,UScalar.cast .U32 rem,?_,?_,?_,?_⟩
  · simp only [AspisR1Post25Sampler.sampler.qm31_div_pass,run,bind_tc_ok]
    rfl
  · rw [castValue,remValue]
    rfl
  · simpa only [decode64, UScalar.val] using outValue
  · rw [castValue]; exact remBound

#print axioms result
end NDH_Qm31Result
