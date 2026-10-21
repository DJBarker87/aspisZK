import IndexedCandidateAddSmallWrapperNatModelV3
import R1SamplerAddBridge

/-! Indexed reference for the exact carry pass compared with Kani. The
candidate extraction remains a reference; no shipped-source adoption occurs. -/
set_option autoImplicit false
namespace AspisR1.R4Transport2AddReference
open Aeneas Aeneas.Std Result
open AspisR1Post25SamplerIndexedAddSmallCandidate
open ExtractedIndexedAddSmallNatModelV1
open SamplerAddDigits

theorem extracted_add_mod_div (digits : Digits) (carry : U32)
    (hcanon : Canonical digits) (hcarry : carry.val ≤ 257) :
    ∃ outCarry : U32, ∃ outDigits : Digits,
      sampler.add_small_base_p digits carry = ok (outCarry != 0#u32, outDigits) ∧
      digitsValue 2147483647 (values outDigits) =
        (digitsValue 2147483647 (values digits) + carry.val) % 2147483647^8 ∧
      outCarry.val =
        (digitsValue 2147483647 (values digits) + carry.val) / 2147483647^8 := by
  obtain ⟨c, ds, hexec, hds, hc⟩ :=
    ExtractedIndexedAddSmallWrapperNatModelV1.add_small_base_p_refines_addDigits
      digits carry hcanon hcarry
  have hv := SamplerAddBridge.addDigits_mod_div (by decide : 0 < 2147483647)
    carry.val (values digits)
  have hlen : (values digits).length = 8 := by
    simp only [values, List.length_map]
    exact digits.property
  rw [hlen] at hv
  exact ⟨c, ds, hexec, by rw [hds]; exact hv.1, hc.trans hv.2⟩

#print axioms extracted_add_mod_div
end AspisR1.R4Transport2AddReference
