import GammaCandidateLowQuotient
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace SDX_CohortGeneric
open AspisR1GammaCaller.DigitsModel AspisR1.SourceSamplerByteRank AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds

theorem map_val_injective (xs ys : List U32) (h : xs.map UScalar.val = ys.map UScalar.val) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have he := List.cons.inj h
      have hxy : x = y := UScalar.eq_of_val_eq he.1
      subst y
      rw [ih ys he.2]
#print axioms map_val_injective

theorem concrete (b : Array U8 32#usize) (expected : Array U32 8#usize) (q0 : U32)
    (hd : values expected = ordinaryDigits (rank b)) (hq : rank b / P^8 = q0.val) :
    AspisR1Post25Sampler.sampler.low_base_p_digits b = ok (expected,q0) := by
  obtain ⟨_,ds,q,run,_,_,_⟩ := AspisR1.ExtractedQM31SamplerIndexedOutputSuccessV5.low_base_p_digits_success b
  have ref := low_candidate_refines b ds q run
  have he : ds = expected := Subtype.ext (map_val_injective _ _ (ref.1.trans hd.symm))
  have hqe : q = q0 := UScalar.eq_of_val_eq (ref.2.trans hq)
  subst ds
  subst q
  exact run
#print axioms concrete
end SDX_CohortGeneric
