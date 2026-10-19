import WideExactNaturalBasisComputableV16
import CompPoly.Univariate.ToPoly.Impl

/-! Minimal executable decoder/encoder declarations, isolated from the polynomial
proof layer so the small program can be checked before any algebraic bridge. -/
namespace AspisWide.NaturalBasisTriangularV4

open AspisWide.NaturalBasisComputable

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)]

def basis (i : Nat) : CompPoly.CPolynomial K := cNaturalLinePoly i

def decode : (n : Nat) → CompPoly.CPolynomial K → Fin (n + 1) → K
  | 0, p => fun _ => p.coeff 0 / (basis (K := K) 0).coeff 0
  | n + 1, p =>
      let c := p.coeff (n + 1) / (basis (K := K) (n + 1)).coeff (n + 1)
      let residual := p - CompPoly.CPolynomial.C c * basis (K := K) (n + 1)
      Fin.lastCases c (decode n residual)

def encode : (n : Nat) → (Fin (n + 1) → K) → CompPoly.CPolynomial K
  | 0, c => CompPoly.CPolynomial.C (c 0) * basis (K := K) 0
  | n + 1, c =>
      encode n (fun i => c i.castSucc) +
        CompPoly.CPolynomial.C (c (Fin.last (n + 1))) * basis (K := K) (n + 1)

#print axioms basis
#print axioms decode
#print axioms encode

end AspisWide.NaturalBasisTriangularV4
