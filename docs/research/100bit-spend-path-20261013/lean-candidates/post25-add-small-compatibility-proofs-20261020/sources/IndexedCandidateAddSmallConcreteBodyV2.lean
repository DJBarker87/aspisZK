import IndexedCandidateAddSmallArithmeticCorrectV5

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1Post25Sampler
open AspisR1.ExtractedAddSmallLoopWritebackV1
open AspisR1.ExtractedAddSmallArithmeticCorrectV1

namespace AspisR1.ExtractedAddSmallConcreteBodyV1

variable [AspisR1Post25Sampler.StdOperationModel]

private abbrev P : Nat := 2147483647

/-- One successful `some digit` loop iteration, without an assumed arithmetic
success premise: canonical digit and bounded addend force the generated
machine pipeline to return its exact modulo digit and carry. -/
theorem body_some_bounded
    (iter : core.slice.iter.IterMut Std.U32)
    (back : core.slice.iter.IterMut Std.U32 → core.slice.iter.IterMut Std.U32)
    (digit addend : Std.U32)
    (iter1 : core.slice.iter.IterMut Std.U32)
    (nextBack : core.slice.iter.IterMut Std.U32 → Option Std.U32 → core.slice.iter.IterMut Std.U32)
    (hnext : core.slice.iter.IteratorIterMut.next iter = .ok (some digit, iter1, nextBack))
    (hdigit : digit.val < P) (haddend : addend.val ≤ 257) :
    ∃ digitOut carryOut,
      sampler.add_small_base_p_loop.body iter back addend =
        .ok (.cont (iter1, fun im => back (nextBack im (some digitOut)), carryOut)) ∧
      digitOut.val = (digit.val + addend.val) % P ∧
      carryOut.val = (digit.val + addend.val) / P ∧
      digitOut.val < P ∧ carryOut.val ≤ 1 := by
  obtain ⟨digitOut, carryOut, harith, hout, hcarry⟩ :=
    arithmeticStep_success digit addend hdigit haddend
  refine ⟨digitOut, carryOut, body_some_writeback iter back addend digit iter1
    nextBack digitOut carryOut hnext harith, hout, hcarry, ?_, ?_⟩
  · rw [hout]
    exact Nat.mod_lt _ (by norm_num [P])
  · have hsmall : digit.val + addend.val < 2 * P := by
      have hcap : P + 257 < 2 * P := by norm_num [P]
      omega
    have hpositive : 0 < P := by norm_num [P]
    have hquot : (digit.val + addend.val) / P < 2 :=
      (Nat.div_lt_iff_lt_mul hpositive).2 (by simpa [Nat.mul_comm] using hsmall)
    change carryOut.val = (digit.val + addend.val) / P at hcarry
    rw [hcarry]
    omega

#print axioms body_some_bounded

end AspisR1.ExtractedAddSmallConcreteBodyV1
