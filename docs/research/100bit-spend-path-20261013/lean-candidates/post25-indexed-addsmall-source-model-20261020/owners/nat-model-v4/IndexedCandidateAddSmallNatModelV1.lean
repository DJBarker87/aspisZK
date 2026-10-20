import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
import IndexedCandidateAddSmallLoopCanonicalV11
import R1SamplerAddBridge
import R1SamplerAddDigits

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error WP
open AspisR1Post25SamplerIndexedAddSmallCandidate
open AspisR1.ExtractedIndexedAddSmallGeneratedOneStepV2
open AspisR1.ExtractedIndexedAddSmallLoopCanonicalV11
open AspisR1.SamplerAddDigits
open AspisR1.SamplerAddBridge

namespace AspisR1.ExtractedIndexedAddSmallNatModelV1

private abbrev P : Nat := 2147483647
abbrev Digits := Array Std.U32 8#usize

def values (digits : Digits) : List Nat := digits.val.map UScalar.val

private def cell (digits : Digits) (j : Nat) (hj : j < 8) : Nat :=
  (digits.val[j]'(by simpa [digits.property] using hj)).val

def Canonical (digits : Digits) : Prop :=
  ∀ j, (hj : j < 8) → cell digits j hj < P

private theorem values_length (digits : Digits) : (values digits).length = 8 := by
  simp only [values, List.length_map]
  have h := digits.property
  change digits.val.length = (8#usize).val at h
  have h8 : (8#usize).val = 8 := by decide
  omega

private theorem values_set_take (digits : Digits) (i : Usize) (d : U32)
    (hi : i.val < 8) :
    (values (digits.set i d)).take (i.val + 1) =
      (values digits).take i.val ++ [d.val] := by
  have hset : values (digits.set i d) = (values digits).set i.val d.val := by
    simp only [values, Aeneas.Std.Array.set_val_eq, List.map_set]
  rw [hset, List.take_succ_eq_append_getElem (by
    simp only [List.length_set, values_length]
    omega)]
  rw [List.take_set_of_le (Nat.le_refl i.val), List.getElem_set_self]

private theorem values_set_drop (digits : Digits) (i : Usize) (d : U32)
    (hi : i.val < 8) :
    (values (digits.set i d)).drop (i.val + 1) =
      (values digits).drop (i.val + 1) := by
  have hset : values (digits.set i d) = (values digits).set i.val d.val := by
    simp only [values, Aeneas.Std.Array.set_val_eq, List.map_set]
  rw [hset, List.drop_set_of_lt (by omega)]

private theorem loop_unroll (digits : Digits) (carry : U32) (i : Usize) :
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

/-- The emitted indexed loop agrees with the little-endian `addDigits` model
on the unprocessed suffix.  The prefix equation records exactly which array
cells have already been written, so the result remains tied to this execution. -/
theorem loop_refines_addDigits (digits : Digits) (carry : U32) (i : Usize)
    (hi : i.val ≤ 8) (hcanon : Canonical digits) (hcarry : carry.val ≤ 257) :
    ∃ outDigits : Digits, ∃ outCarry : U32,
      sampler.add_small_base_p_loop digits carry i = .ok (outDigits, outCarry) ∧
      values outDigits = (values digits).take i.val ++
        (addDigits P carry.val ((values digits).drop i.val)).1 ∧
      outCarry.val = (addDigits P carry.val ((values digits).drop i.val)).2 := by
  induction hmeasure : 8 - i.val using Nat.strong_induction_on generalizing digits carry i with
  | h n ih =>
    by_cases hlt : i.val < 8
    · have hbound : i.val < digits.length := by
        change i.val < digits.val.length
        have hlen := values_length digits
        simp only [values, List.length_map] at hlen
        omega
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
      obtain ⟨outDigits, outCarry, hexec, hprefix, htailCarry⟩ :=
        ih (8 - next.val) hmeasureNext (digits := digits.set i digitOut)
          (carry := carryOut) (i := next) hnextBound hcanon' hcarryOut rfl
      have hvnext : next.val = i.val + 1 := by omega
      have hget : (values digits)[i.val]'(by
          rw [values_length]
          exact hlt) = digit.val := by
        have hv := congrArg UScalar.val hvalue
        simpa [values, cell] using hv.symm
      have hdrop : (values digits).drop i.val =
          digit.val :: ((values digits).drop (i.val + 1)) := by
        rw [List.drop_eq_getElem_cons (by rw [values_length]; exact hlt), hget]
      have htakeSet : (values (digits.set i digitOut)).take next.val =
          (values digits).take i.val ++ [digitOut.val] := by
        rw [hvnext]
        exact values_set_take digits i digitOut hlt
      have hdropSet : (values (digits.set i digitOut)).drop next.val =
          (values digits).drop (i.val + 1) := by
        rw [hvnext]
        exact values_set_drop digits i digitOut hlt
      have hmodel : addDigits P carry.val ((values digits).drop i.val) =
          (digitOut.val ::
            (addDigits P carryOut.val ((values digits).drop (i.val + 1))).1,
            (addDigits P carryOut.val ((values digits).drop (i.val + 1))).2) := by
        rw [hdrop]
        simp only [addDigits]
        rw [hremP, hquoP]
      refine ⟨outDigits, outCarry, ?_, ?_, ?_⟩
      · rw [loop_unroll, hstep]
        simp only [bind_tc_ok]
        simpa using hexec
      · calc
          values outDigits =
              (values (digits.set i digitOut)).take next.val ++
                (addDigits P carryOut.val
                  ((values (digits.set i digitOut)).drop next.val)).1 := hprefix
          _ = (values digits).take i.val ++
                [digitOut.val] ++
                (addDigits P carryOut.val
                  ((values digits).drop (i.val + 1))).1 := by
                  rw [htakeSet, hdropSet]
          _ = (values digits).take i.val ++
                (addDigits P carry.val ((values digits).drop i.val)).1 := by
                  rw [hmodel]
                  simp only [List.append_assoc, List.singleton_append]
      · calc
          outCarry.val =
              (addDigits P carryOut.val
                ((values (digits.set i digitOut)).drop next.val)).2 := htailCarry
          _ = (addDigits P carryOut.val
                ((values digits).drop (i.val + 1))).2 := by rw [hdropSet]
          _ = (addDigits P carry.val ((values digits).drop i.val)).2 := by
                rw [hmodel]
    · have hi8 : i.val = 8 := by omega
      have hdone : sampler.add_small_base_p_loop.body digits carry i =
          .ok (.done (digits, carry)) := by
        have hg : ¬ i < 8#usize := by change ¬ i.val < 8; omega
        unfold sampler.add_small_base_p_loop.body
        simp [hg]
      refine ⟨digits, carry, ?_, ?_, ?_⟩
      · rw [loop_unroll, hdone]
        simp only [bind_tc_ok]
      · rw [hi8]
        have htake : (values digits).take 8 = values digits :=
          List.take_of_length_le (by rw [values_length])
        have hdrop : (values digits).drop 8 = [] :=
          List.drop_of_length_le (by rw [values_length])
        rw [htake, hdrop]
        simp [addDigits]
      · rw [hi8]
        have hdrop : (values digits).drop 8 = [] :=
          List.drop_of_length_le (by rw [values_length])
        rw [hdrop]
        simp [addDigits]
termination_by 8 - i.val
decreasing_by omega

theorem loop_zero_refines_addDigits (digits : Digits) (carry : U32)
    (hcanon : Canonical digits) (hcarry : carry.val ≤ 257) :
    ∃ outDigits : Digits, ∃ outCarry : U32,
      sampler.add_small_base_p_loop digits carry 0#usize = .ok (outDigits, outCarry) ∧
      values outDigits = (addDigits P carry.val (values digits)).1 ∧
      outCarry.val = (addDigits P carry.val (values digits)).2 := by
  obtain ⟨outDigits, outCarry, hexec, hvalues, hcarry'⟩ :=
    loop_refines_addDigits digits carry 0#usize (by decide) hcanon hcarry
  refine ⟨outDigits, outCarry, hexec, ?_, hcarry'⟩
  simpa using hvalues

/-- The generated output and carry satisfy the exact radix-P remainder and
quotient equations for the original positional digit value plus the addend. -/
theorem loop_zero_model_value_quotient (digits : Digits) (carry : U32)
    (hcanon : Canonical digits) (hcarry : carry.val ≤ 257) :
    ∃ outDigits : Digits, ∃ outCarry : U32,
      sampler.add_small_base_p_loop digits carry 0#usize = .ok (outDigits, outCarry) ∧
      digitsValue P (values outDigits) =
        (digitsValue P (values digits) + carry.val) % P ^ 8 ∧
      outCarry.val = (digitsValue P (values digits) + carry.val) / P ^ 8 := by
  obtain ⟨outDigits, outCarry, hexec, hvalues, hcarry'⟩ :=
    loop_zero_refines_addDigits digits carry hcanon hcarry
  have hmodel := addDigits_mod_div (p := P) (by norm_num [P]) carry.val (values digits)
  refine ⟨outDigits, outCarry, hexec, ?_, ?_⟩
  · rw [hvalues]
    simpa only [values_length] using hmodel.1
  · rw [hcarry']
    simpa only [values_length] using hmodel.2

#print axioms loop_refines_addDigits
#print axioms loop_zero_refines_addDigits
#print axioms loop_zero_model_value_quotient

end AspisR1.ExtractedIndexedAddSmallNatModelV1
