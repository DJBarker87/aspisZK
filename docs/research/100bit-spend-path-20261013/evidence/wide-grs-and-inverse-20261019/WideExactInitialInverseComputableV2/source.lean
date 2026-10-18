import CompPoly.Univariate.Lagrange
set_option autoImplicit false
namespace AspisWide.InitialInverseComputable

/-- Computable finite-node Lagrange reconstruction for the inverse
stereographic sampling values. The caller supplies only `d+1` nodes; this
never enumerates the ambient field. -/
def decodeFractionalLiftC
    {K : Type} [BEq K] [Field K] [LawfulBEq K]
    (d : Nat) (nodes : Fin (d + 1) → K) (q : CompPoly.CPolynomial K) :
    CompPoly.CPolynomial K :=
  CompPoly.CPolynomial.CLagrange.interpolate Finset.univ nodes fun i =>
    CompPoly.CPolynomial.eval ((1 - nodes i) / (1 + nodes i)) q *
      ((1 + ((1 - nodes i) / (1 + nodes i))) ^ d)⁻¹

theorem decodeFractionalLiftC_toPoly
    {K : Type} [BEq K] [Field K] [LawfulBEq K]
    (d : Nat) (nodes : Fin (d + 1) → K) (q : CompPoly.CPolynomial K) :
    (decodeFractionalLiftC d nodes q).toPoly =
      Lagrange.interpolate Finset.univ nodes (fun i =>
        CompPoly.CPolynomial.eval ((1 - nodes i) / (1 + nodes i)) q *
          ((1 + ((1 - nodes i) / (1 + nodes i))) ^ d)⁻¹) := by
  exact CompPoly.CPolynomial.CLagrange.cinterpolate_eq_interpolate

#print axioms decodeFractionalLiftC_toPoly
end AspisWide.InitialInverseComputable
