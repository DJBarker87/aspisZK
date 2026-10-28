import NBA_AddCarry
import IndexedCandidateAddSmallWrapperNatModelV3
set_option autoImplicit false
namespace AspisR1.NBA_AddPair
open Aeneas Aeneas.Std Result
open ExtractedIndexedAddSmallNatModelV1

theorem source (digits : Digits) (carry : U32) (canonical : Canonical digits)
    (small : carry.val≤257) (out : List Nat) (final : Nat)
    (trace : NBA_AddCarry.Trace (values digits) carry.val out final) :
    ∃ outCarry : U32, ∃ outDigits : Digits,
      AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits carry=
        ok (outCarry != 0#u32,outDigits) ∧ values outDigits=out ∧ outCarry.val=final := by
  obtain ⟨c,d,call,value,cv⟩ :=
    ExtractedIndexedAddSmallWrapperNatModelV1.add_small_base_p_refines_addDigits digits carry canonical small
  have step := NBA_AddCarry.source trace
  rw [step] at value cv
  exact ⟨c,d,call,value,cv⟩

#print axioms source
end AspisR1.NBA_AddPair
