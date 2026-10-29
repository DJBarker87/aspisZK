import NDH_Decode8
import LPk_Cohort
set_option autoImplicit false
namespace NDH_NativeDomains
open Aeneas Aeneas.Std Result
open AspisR1.SourceSamplerByteRank

theorem low_digits_decode_domain (block : Array U8 32#usize) :
    ∃ (digits : Array U32 8#usize) (quotient : U32),
      AspisR1Post25Sampler.sampler.low_base_p_digits block=ok (digits,quotient) ∧
      (∀ i : Fin 8, (NDH_Decode8.digit digits i).val<2147483647) ∧
      quotient.val≤256 := by
  obtain ⟨digits,q,run,_,_,qb,canon⟩ := LPk_Cohort.all_blocks block
  refine ⟨digits,q,run,?_,qb⟩
  intro i
  apply canon
  change (NDH_Decode8.digit digits i).val ∈ digits.val.map UScalar.val
  apply List.mem_map.mpr
  exact ⟨NDH_Decode8.digit digits i,
    List.getElem_mem (by have := digits.property; change digits.val.length=8 at this; omega),rfl⟩

#print axioms low_digits_decode_domain
end NDH_NativeDomains
