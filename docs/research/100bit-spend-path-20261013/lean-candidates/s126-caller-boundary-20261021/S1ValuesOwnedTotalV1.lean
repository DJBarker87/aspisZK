import S1ValuesOwnedOuterTotalV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedTotal
open Aeneas Aeneas.Std Result WP AspisS1ValuesOwned

/-- TOTAL complete reference under the checked doubling range. No alignment,
output-size equality, successful codec result or loop return is assumed.
Malformed input/output dimensions retain their actual CodecError.Length. -/
@[step] theorem reference_spec (input output : Buffer)
    (doubling : 2*input.length ≤ Usize.max) :
    values_owned_reference input output ⦃ _ => True ⦄ := by
  unfold values_owned_reference
  step* <;> scalar_tac

theorem reference_total (input output : Buffer)
    (doubling : 2*input.length ≤ Usize.max) :
    ∃ result, values_owned_reference input output=ok result := by
  obtain ⟨result,call,_⟩ := spec_imp_exists (reference_spec input output doubling)
  exact ⟨result,call⟩

#print axioms reference_spec
#print axioms reference_total
end AspisS1ValuesOwnedTotal
