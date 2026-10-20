import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
import IndexedCandidateAddSmallNatModelV1
import R1SamplerAddBridge

set_option autoImplicit false

open Aeneas Aeneas.Std Result
open AspisR1Post25SamplerIndexedAddSmallCandidate
open AspisR1.ExtractedIndexedAddSmallNatModelV1
open AspisR1.SamplerAddDigits
open AspisR1.SamplerAddBridge

namespace AspisR1.ExtractedIndexedAddSmallWrapperNatModelV1

private abbrev P : Nat := 2147483647

/-- The actual generated candidate entrypoint is exactly the checked loop
result packaged with its final-carry nonzero flag.  The digit output and carry
remain related to the same execution and to the `addDigits` Nat model. -/
theorem add_small_base_p_refines_addDigits (digits : Digits) (carry : U32)
    (hcanon : Canonical digits) (hcarry : carry.val ≤ 257) :
    ∃ outCarry : U32, ∃ outDigits : Digits,
      sampler.add_small_base_p digits carry =
        .ok (outCarry != 0#u32, outDigits) ∧
      values outDigits = (addDigits P carry.val (values digits)).1 ∧
      outCarry.val = (addDigits P carry.val (values digits)).2 := by
  obtain ⟨outDigits, outCarry, hexec, hvalues, hcarry'⟩ :=
    loop_zero_refines_addDigits digits carry hcanon hcarry
  refine ⟨outCarry, outDigits, ?_, hvalues, hcarry'⟩
  unfold sampler.add_small_base_p
  rw [hexec]
  rfl

/-- The entrypoint's returned digits and final-carry flag satisfy the exact
modulo/division equations for the input positional value plus the addend. -/
theorem add_small_base_p_model_value_quotient (digits : Digits) (carry : U32)
    (hcanon : Canonical digits) (hcarry : carry.val ≤ 257) :
    ∃ outCarry : U32, ∃ outDigits : Digits,
      sampler.add_small_base_p digits carry =
        .ok (outCarry != 0#u32, outDigits) ∧
      digitsValue P (values outDigits) =
        (digitsValue P (values digits) + carry.val) % P ^ 8 ∧
      outCarry.val = (digitsValue P (values digits) + carry.val) / P ^ 8 := by
  obtain ⟨outCarry, outDigits, hrun, hvalues, hcarry'⟩ :=
    add_small_base_p_refines_addDigits digits carry hcanon hcarry
  have hmodel := addDigits_mod_div (p := P) (by norm_num [P]) carry.val (values digits)
  refine ⟨outCarry, outDigits, hrun, ?_, ?_⟩
  · rw [hvalues]
    simpa only [values_length] using hmodel.1
  · rw [hcarry']
    simpa only [values_length] using hmodel.2

#print axioms add_small_base_p_refines_addDigits
#print axioms add_small_base_p_model_value_quotient

end AspisR1.ExtractedIndexedAddSmallWrapperNatModelV1
