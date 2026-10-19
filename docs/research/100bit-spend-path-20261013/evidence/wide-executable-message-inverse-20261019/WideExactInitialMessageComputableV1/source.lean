import WideExactInitialParityCBridgeV9
import WideExactNaturalBasisTriangularV14

set_option autoImplicit false

namespace AspisWide.InitialMessageComputableV1

open CompPoly
open AspisWide.InitialParityCBridgeV9
open AspisWide.InitialInverseComputable
open AspisWide.NaturalBasisTriangularV4

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)]

/-- Executable 1024-coefficient decoder from the RR output polynomial. It
extracts even/odd numerator coefficients, applies the computable fractional
lift interpolation, then inverts the natural basis by triangular cancellation. -/
def decodeMessage (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K)
    (q : CPolynomial K) : Fin 1024 → K := by
  let p0 := decodeFractionalLiftC 512 nodes0 (evenC q)
  let p1 := decodeFractionalLiftC 511 nodes1 (oddC q)
  exact fun k =>
    if hk : k.val % 2 = 0 then
      decode 511 p0 ⟨k.val / 2, by omega⟩
    else
      decode 511 p1 ⟨k.val / 2, by omega⟩

#print axioms decodeMessage

end AspisWide.InitialMessageComputableV1
