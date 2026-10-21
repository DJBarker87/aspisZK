import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
import IndexedCandidateAddSmallGeneratedOneStepV1

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error WP
open AspisR1Post25SamplerIndexedAddSmallCandidate
open AspisR1.ExtractedIndexedAddSmallGeneratedOneStepV2

namespace AspisR1.ExtractedIndexedAddSmallLoopCanonicalV11

abbrev Digits := Array Std.U32 8#usize
private abbrev P : Nat := 2147483647

private theorem digits_length (digits : Digits) : digits.val.length = 8 := by
  have hp := digits.property
  change digits.val.length = (8#usize).val at hp
  have h8 : (8#usize).val = 8 := by decide
  omega

def cell (digits : Digits) (j : Nat) (hj : j < 8) : Nat :=
  (digits.val[j]'(by simpa [digits.property] using hj)).val

def Canonical (digits : Digits) : Prop :=
  ∀ j, (hj : j < 8) → cell digits j hj < P

private theorem body_unroll (digits : Digits) (carry : U32) (i : Usize) :
    sampler.add_small_base_p_loop digits carry i = (do
      let flow ← sampler.add_small_base_p_loop.body digits carry i
      match flow with
      | .cont (digits1, carry1, i1) => sampler.add_small_base_p_loop digits1 carry1 i1
      | .done out => ok out) := by
  conv_lhs =>
    unfold sampler.add_small_base_p_loop
    rw [loop]
  cases hbody : sampler.add_small_base_p_loop.body digits carry i with
  | fail e => simp only [hbody, bind_tc_fail]
  | div => simp only [hbody, bind_tc_div]
  | ok flow =>
    cases flow with
    | done out => simp only [hbody, bind_tc_ok]
    | cont next => simp only [hbody, bind_tc_ok]; rfl

/-- A symbolic induction over the remaining indices proves the emitted
indexed candidate loop always succeeds on canonical base-P digits and a small
carry, preserving both invariants. -/
theorem loop_success_canonical (digits : Digits) (carry : U32) (i : Usize)
    (hi : i.val ≤ 8) (hcanon : Canonical digits) (hcarry : carry.val ≤ 257) :
    ∃ outDigits : Digits, ∃ outCarry : U32,
      sampler.add_small_base_p_loop digits carry i = .ok (outDigits, outCarry) ∧
      Canonical outDigits ∧ outCarry.val ≤ 257 := by
  induction hmeasure : 8 - i.val using Nat.strong_induction_on generalizing digits carry i with
  | h n ih =>
    by_cases hlt : i.val < 8
    · have hbound : i.val < digits.length := by
        change i.val < digits.val.length
        rw [digits_length]
        exact hlt
      obtain ⟨digit, hindex, hvalue⟩ :=
        WP.spec_imp_exists (Array.index_usize_spec digits i hbound)
      have hdigit : digit.val < P := by
        have heq : digit.val = cell digits i.val hlt := by
          have hv := congrArg UScalar.val hvalue
          simpa [cell] using hv
        rw [heq]
        exact hcanon i.val hlt
      obtain ⟨digitOut, carryOut, next, hstep, hrem, hquo, hnext⟩ :=
        body_step digits carry i digit hlt hindex hdigit hcarry
      have hremP : digitOut.val = (digit.val + carry.val) % P := by
        change digitOut.val = (digit.val + carry.val) % 2147483647 at hrem
        exact hrem
      have hquoP : carryOut.val = (digit.val + carry.val) / P := by
        change carryOut.val = (digit.val + carry.val) / 2147483647 at hquo
        exact hquo
      have hcarryOut : carryOut.val ≤ 257 := by
        have hsumSmall : digit.val + carry.val < 2 * P := by
          have hbound' : P + 257 < 2 * P := by norm_num [P]
          omega
        have hp' : 0 < P := by norm_num [P]
        have hq : (digit.val + carry.val) / P < 2 :=
          (Nat.div_lt_iff_lt_mul hp').2 (by simpa [Nat.mul_comm] using hsumSmall)
        rw [hquoP]
        omega
      have hcanon' : Canonical (digits.set i digitOut) := by
        intro j hjlt
        have hjSet : j < (digits.val.set i.val digitOut).length := by simpa using hjlt
        have hjOld : j < digits.val.length := by simpa [digits.property] using hjlt
        change ((digits.val.set i.val digitOut)[j]'hjSet).val < P
        by_cases heq : i.val = j
        · have hcell : (digits.val.set i.val digitOut)[j]'hjSet = digitOut := by
            have hself := List.getElem_set_self (l := digits.val) (i := i.val) (a := digitOut)
              (by simpa [heq] using hjSet)
            simpa [heq] using hself
          rw [hcell, hremP]
          exact Nat.mod_lt _ (by norm_num [P])
        · have hcell : (digits.val.set i.val digitOut)[j]'hjSet =
              digits.val[j]'hjOld := by
            simpa using (List.getElem_set_ne (l := digits.val) (i := i.val) (j := j)
              (by omega) hjSet)
          rw [hcell]
          exact hcanon j hjlt
      have hnextBound : next.val ≤ 8 := by omega
      have hmeasureNext : 8 - next.val < n := by omega
      obtain ⟨outDigits, outCarry, hexec, houtCanon, houtCarry⟩ :=
        ih (8 - next.val) hmeasureNext (digits := digits.set i digitOut)
          (carry := carryOut) (i := next) hnextBound hcanon' hcarryOut rfl
      refine ⟨outDigits, outCarry, ?_, houtCanon, houtCarry⟩
      rw [body_unroll, hstep]
      simp only [bind_tc_ok]
      simpa using hexec
    · have hdone : sampler.add_small_base_p_loop.body digits carry i =
          .ok (.done (digits, carry)) := by
        have hg : ¬ i < 8#usize := by change ¬ i.val < 8; omega
        unfold sampler.add_small_base_p_loop.body
        simp [hg]
      refine ⟨digits, carry, ?_, hcanon, hcarry⟩
      rw [body_unroll, hdone]
      simp only [bind_tc_ok]

theorem loop_zero_success (digits : Digits) (carry : U32)
    (hcanon : Canonical digits) (hcarry : carry.val ≤ 257) :
    ∃ outDigits : Digits, ∃ outCarry : U32,
      sampler.add_small_base_p_loop digits carry 0#usize = .ok (outDigits, outCarry) ∧
      Canonical outDigits ∧ outCarry.val ≤ 257 := by
  apply loop_success_canonical digits carry 0#usize (by decide) hcanon hcarry

#print axioms loop_success_canonical
#print axioms loop_zero_success

end AspisR1.ExtractedIndexedAddSmallLoopCanonicalV11
