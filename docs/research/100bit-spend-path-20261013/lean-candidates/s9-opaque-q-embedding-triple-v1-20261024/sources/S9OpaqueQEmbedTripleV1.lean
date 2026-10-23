import S9SharedScalarModelValuesV1
set_option autoImplicit false
noncomputable section
namespace AspisR1S9OpaqueQEmbedTripleV1
open AspisR1S9SharedScalarModelValuesV1
abbrev Q := ExactQM
abbrev W := AspisWideTower.WideExact
noncomputable def semiringMul {K : Type} [CommSemiring K] (x y : K) : K := x*y
/-- Tiny opaque-scalar operator bridges, isolated before any source row. -/
theorem q_mul_operator (x y : Q) : x*y=semiringMul x y := by rfl
theorem wide_mul_operator (x y : W) : x*y=semiringMul x y := by rfl
private theorem mapped_mul {A B : Type} [CommSemiring A] [CommSemiring B]
    (iota : A →+* B) (x y : A) :
    iota (semiringMul x y)=semiringMul (iota x) (iota y) := map_mul iota x y
/-- Concrete native model carrier operations on three opaque factors. -/
theorem embedQ_mul (x y : Q) : embedQ (x*y)=embedQ x*embedQ y := by
  have h : embedQ (semiringMul x y)=semiringMul (embedQ x) (embedQ y) :=
    mapped_mul (algebraMap Q W) x y
  exact (congrArg embedQ (q_mul_operator x y)).trans
    (h.trans (wide_mul_operator (embedQ x) (embedQ y)).symm)
theorem embedQ_triple (x y z : Q) :
    embedQ (x*y*z)=(embedQ x*embedQ y)*embedQ z := by
  exact (embedQ_mul (x*y) z).trans
    (congrArg (fun t : W => t*embedQ z) (embedQ_mul x y))
#print axioms q_mul_operator
#print axioms wide_mul_operator
#print axioms embedQ_mul
#print axioms embedQ_triple
end AspisR1S9OpaqueQEmbedTripleV1
end
