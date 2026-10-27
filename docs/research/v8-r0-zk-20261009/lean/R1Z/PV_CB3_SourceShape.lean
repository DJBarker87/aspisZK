import R1Z.PV_CB3_SourcePass
namespace R1Z.PV_CB3_SourceShape
open Aeneas Aeneas.Std Result
open PV_CB3_SourcePass (pass values)
open PV_CB3_SamplerWord (base radix)
set_option autoImplicit false

/-- Exact source-step composition supplies both shape and range; neither is
assumed as a successful-output premise. -/
theorem total_shape (words : List U32) :
    ∃ (q : List U32) (r : U64), pass words = ok (q,r) ∧
      q.length = words.length ∧ r.val < base := by
  obtain ⟨q,r,h,hq,hr⟩ := PV_CB3_SourcePass.total words
  have hl := congrArg List.length hq
  simp only [values, List.length_map, PV_CB3_SamplerDivision.length_preserved] at hl
  refine ⟨q,r,h,hl,?_⟩
  rw [hr]
  exact PV_CB3_SamplerDivision.remainder_lt base radix (by unfold base; omega) _

theorem total_value (words : List U32) :
    ∃ (q : List U32) (r : U64), pass words = ok (q,r) ∧
      base * PV_CB3_SamplerCarry.value radix (values q) + r.val =
        PV_CB3_SamplerCarry.value radix (values words) := by
  obtain ⟨q,r,h,hq,hr⟩ := PV_CB3_SourcePass.total words
  refine ⟨q,r,h,?_⟩
  rw [hq,hr]
  exact PV_CB3_SamplerDivision.value_conserved base radix _

theorem quotient_value (words : List U32) :
    ∃ (q : List U32) (r : U64), pass words = ok (q,r) ∧
      PV_CB3_SamplerCarry.value radix (values words) / base =
        PV_CB3_SamplerCarry.value radix (values q) := by
  obtain ⟨q,r,h,hq,_⟩ := PV_CB3_SourcePass.total words
  refine ⟨q,r,h,?_⟩
  rw [hq]
  exact PV_CB3_SamplerDivision.quotient_value base radix (by unfold base; omega) _

#print axioms total_shape
#print axioms total_value
#print axioms quotient_value
end R1Z.PV_CB3_SourceShape
