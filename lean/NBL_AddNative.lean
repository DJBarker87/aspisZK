import NBA_AddPair
import LPk_Result
set_option autoImplicit false
namespace AspisR1.NBL_AddNative
open Aeneas Aeneas.Std Result
open ExtractedIndexedAddSmallNatModelV1

/-- Complete native add-small carrier from the checked per-digit trace.
The output array/carry are ports of that trace, not supplied model-call results. -/
theorem source (digits : Digits) (carry : U32) (canonical : Canonical digits)
    (small : carry.val≤257) (out : Digits) (last : U32)
    (trace : NBA_AddCarry.Trace (values digits) carry.val (values out) last.val) :
    AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits carry=
      ok (last != 0#u32,out) := by
  obtain ⟨c,d,call,value,cv⟩ := NBA_AddPair.source digits carry canonical small (values out) last.val trace
  have ce : c=last := UScalar.eq_of_val_eq cv
  have de : d=out := Subtype.ext (LPk_Result.values_injective _ _ value)
  simpa only [ce,de] using call

/-- Canonicality of the produced array is derived after every carry pass. -/
theorem canonical (digits : Digits) (carry : U32) (out : Digits) (last : U32)
    (trace : NBA_AddCarry.Trace (values digits) carry.val (values out) last.val) :
    Canonical out := by
  have same := congrArg Prod.fst (NBA_AddCarry.source trace)
  dsimp only [Prod.fst] at same
  intro j hj
  change (out.val[j]'(by simpa [out.property] using hj)).val < 2147483647
  have member : (out.val[j]'(by simpa [out.property] using hj)).val ∈ values out := by
    exact List.mem_map.mpr ⟨_,List.getElem_mem _,rfl⟩
  have all := SamplerAddDigits.addDigits_output_digits_lt 2147483647 carry.val (values digits) (by decide)
  rw [same] at all
  exact all _ member

#print axioms source
#print axioms canonical
end AspisR1.NBL_AddNative
