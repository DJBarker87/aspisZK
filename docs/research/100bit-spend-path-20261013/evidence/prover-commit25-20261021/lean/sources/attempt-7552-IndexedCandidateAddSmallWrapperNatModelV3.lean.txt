import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
import IndexedCandidateAddSmallNatModelV1
import R1SamplerAddDigits

set_option autoImplicit false

open Aeneas Aeneas.Std Result
open AspisR1Post25SamplerIndexedAddSmallCandidate
open AspisR1.ExtractedIndexedAddSmallNatModelV1
open AspisR1.SamplerAddDigits

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


#print axioms add_small_base_p_refines_addDigits

end AspisR1.ExtractedIndexedAddSmallWrapperNatModelV1
