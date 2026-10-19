import WideExactInitialInverseV5
import WideExactInitialInverseComputableV2

set_option autoImplicit false
namespace AspisWide.InitialInverseBridge
variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

theorem decodeFractionalLiftC_toPoly_eq
    (d : Nat) (nodes : Fin (d + 1) → K)
    (havoid : ∀ i, nodes i ≠ -1) (q : CompPoly.CPolynomial K) :
    (AspisWide.InitialInverseComputable.decodeFractionalLiftC d nodes q).toPoly =
      AspisWide.InitialInverse.decodeFractionalLift d nodes havoid q.toPoly := by
  rw [AspisWide.InitialInverseComputable.decodeFractionalLiftC_toPoly]
  unfold AspisWide.InitialInverse.decodeFractionalLift
  congr 1
  funext i
  rw [CompPoly.CPolynomial.eval_toPoly]

#print axioms decodeFractionalLiftC_toPoly_eq
end AspisWide.InitialInverseBridge
