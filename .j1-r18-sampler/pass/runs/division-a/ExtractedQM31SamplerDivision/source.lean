import ExtractedQM31SamplerPassLoop

/-! The actual complete source pass, with its whole returned quotient array. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerDivision
open Aeneas Aeneas.Std Result
open AspisR1Qm31SamplerIndex
open SamplerMachineBounds SamplerWordPass ExtractedQM31SamplerPassLoop

theorem div_pass_correct (rank : Array U32 8#usize) :
    ∃ (quotient : Array U32 8#usize) (digit : U32),
      sampler.qm31_div_pass rank = ok (quotient, digit) ∧
      (words quotient).reverse = (machineProcess 0 (words rank).reverse).2 ∧
      digit.val = (machineProcess 0 (words rank).reverse).1.toNat ∧
      digit.val < P := by
  obtain ⟨quotient, rem, hexec, hrem, hwords, hbound⟩ :=
    loop_correct rank (0#u64) (8#usize) (by exact P_pos) (by decide)
  have htake : (words rank).take 8 = words rank := by
    rw [← words_length rank]
    exact List.take_length
  have hdrop : (words rank).drop 8 = [] := by
    rw [← words_length rank]
    exact List.drop_length
  have hzero : decode64 (0#u64) = 0 := rfl
  change rem.val = (machineProcess (decode64 (0#u64)) ((words rank).take 8).reverse).1.toNat at hrem
  change words quotient =
    (machineProcess (decode64 (0#u64)) ((words rank).take 8).reverse).2.reverse
      ++ (words rank).drop 8 at hwords
  rw [hzero, htake] at hrem
  rw [hzero, htake, hdrop, List.append_nil] at hwords
  let digit : U32 := UScalar.cast .U32 rem
  have hvdigit : digit.val = rem.val := by
    rw [show digit.val = rem.val % 2^32 from UScalar.cast_val_eq _ _]
    apply Nat.mod_eq_of_lt
    exact lt_trans hbound (by norm_num [P])
  refine ⟨quotient, digit, ?_, ?_, ?_, ?_⟩
  · simp only [sampler.qm31_div_pass, hexec, lift, bind_tc_ok, digit]
  · rw [hwords, List.reverse_reverse]
  · rw [hvdigit]; exact hrem
  · rw [hvdigit]; exact hbound

#print axioms div_pass_correct

end AspisR1.ExtractedQM31SamplerDivision
