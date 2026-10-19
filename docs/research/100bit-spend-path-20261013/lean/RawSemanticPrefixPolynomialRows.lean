import R1SemanticPrefixCodec

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawSemanticPrefixPolynomialRows

open AspisR1.SemanticRecordCodec AspisR1.SemanticCoefficientCodec

/-- Extract the coefficient vector at a polynomial row using only the typed
row codec. Rows 15 through 24 are forced to have the polynomial constructor
by `validRow`; no semantic-view or R0P import is needed. -/
def coefficientsAt (values : AspisR1.SemanticPrefixCodec.Full) (j : Fin 10) :
    Coefficients :=
  match values ⟨15 + j.val, by omega⟩ with
  | ⟨.empty, h⟩ => by
      have h' : 15 + j.val < 2 ∨
          (3 ≤ 15 + j.val ∧ 15 + j.val < 14) := by
        simpa [validRow] using h
      omega
  | ⟨.c2Root _, h⟩ => by
      have h' : 15 + j.val = 2 := by simpa [validRow] using h
      omega
  | ⟨.maskSum _, h⟩ => by
      have h' : 15 + j.val = 14 := by simpa [validRow] using h
      omega
  | ⟨.polynomial coefficients, _⟩ => coefficients

theorem coefficientsAt_payload (values : AspisR1.SemanticPrefixCodec.Full)
    (j : Fin 10) :
    (values ⟨15 + j.val, by omega⟩).val =
      .polynomial (coefficientsAt values j) := by
  have hj : j.val < 10 := j.isLt
  unfold coefficientsAt
  cases values ⟨15 + j.val, by omega⟩ with
  | mk payload hvalid =>
      cases payload with
      | empty =>
          have h' : 15 + j.val < 2 ∨
              (3 ≤ 15 + j.val ∧ 15 + j.val < 14) := by
            simpa [validRow] using hvalid
          omega
      | c2Root root =>
          have h' : 15 + j.val = 2 := by simpa [validRow] using hvalid
          omega
      | maskSum value =>
          have h' : 15 + j.val = 14 := by simpa [validRow] using hvalid
          omega
      | polynomial coefficients => rfl

#print axioms coefficientsAt_payload
end AspisR1PublicPreparation.RawSemanticPrefixPolynomialRows
