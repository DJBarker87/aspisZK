import S9SharedContiguousContractionV1
set_option autoImplicit false
open scoped BigOperators
namespace AspisR1S9SharedContiguousTransportV1
open AspisR1S9SharedContiguousContractionV1
/-- Abstract-field transport keeps source decoders outside kernel unification.
All source matrix entries remain parameters, rather than unfolded read code. -/
theorem transport_source_sum {E : Type*} [CommSemiring E]
    (matrix : Fin 4 → Fin 16 → E) (flat : Fin 64 → E)
    (low : Fin 16 → E) (high : Fin 4 → E) (value : E)
    (hindex : ∀ s j,matrix s j=flat (sourceIndex s j))
    (hvalue : value=∑ s : Fin 4,(∑ j : Fin 16,matrix s j*low j)*high s) :
    value=∑ i : Fin 64,flat i*tensorWeight low high i := by
  have hr : (∑ s : Fin 4,(∑ j : Fin 16,matrix s j*low j)*high s)=
      ∑ s : Fin 4,(∑ j : Fin 16,flat (sourceIndex s j)*low j)*high s := by
    apply Finset.sum_congr rfl
    intro s _
    apply congrArg (fun x : E => x*high s)
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun x : E => x*low j) (hindex s j)
  exact hvalue.trans (hr.trans (contiguous_contract flat low high).symm)
#print axioms transport_source_sum
end AspisR1S9SharedContiguousTransportV1
