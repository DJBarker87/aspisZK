import AspisV8R19.R684FullSourceMomentIdentity
import AspisV8R19.R861SemanticMaskFinishCoins
import AspisV8R19.R686AllBetaJointGCorrection
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R863SemanticStructuredMoment
open AspisR19 AspisV8R17 HighRepairInvariant
open R684FullSourceMomentIdentity R861SemanticMaskFinishCoins
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem semantic_structured_moment (half quarter a b c kappa tau : F)
    (z : Fin 10 → F) (semanticZ : RoundCoins F 10)
    (q : Index 256 → F) (hquarter : quarter ≠ 0)
    (hp1 : sourcePointFunctional (SourceStatementPoints.points z 1)
      (indexedMask half a b c q) = 0)
    (hp2 : sourcePointFunctional (SourceStatementPoints.points z 2)
      (indexedMask half a b c q) = 0)
    (hbalance : ∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c q r = 0)
    (htail21 : flattenFull q 1021 = 0)
    (htail22 : flattenFull q 1022 = 0)
    (htail23 : flattenFull q 1023 = 0)
    (hsemanticCoins : ∑ i : Fin 271, maskWeights271 half semanticZ i *
      actualCoin (indexedMask half a b c q) i = 0) :
    (∑ d : Fin 256, ∑ s : Fin 4,
      q (d,s) * fullWeight half a b c kappa tau z
        (maskWeights271 half semanticZ) true (d,s)) = 0 := by
  have hpair : (∑ r : Fin 1024,
      TwoSwapSourceG.original
        (AspisR19.SourceGConstant.finishCoins half (maskWeights271 half semanticZ)) r *
        indexedMask half a b c q r) = 0 := by
    rw [R861SemanticMaskFinishCoins.finishCoins_semantic_mask]
    rw [R561.original_pairing]
    simpa only [R645TwoSwapHighDirections.actualCoin] using hsemanticCoins
  have hboundary : fullRelation half quarter a b c kappa tau z
      (maskWeights271 half semanticZ) true q 0 +
      fullRelation half quarter a b c kappa tau z
        (maskWeights271 half semanticZ) true q 4 = 0 := by
    rw [R684FullSourceMomentIdentity.full_source_moment_identity]
    simp only [Bool.true_eq_true, if_true, hpair, hp1, hp2, hbalance,
      htail21, htail22, htail23]
    ring
  have hcoeff := R653SourceCoefficientBoundary.coefficient_boundary 256 quarter q
    (fullWeight half a b c kappa tau z (maskWeights271 half semanticZ) true)
  change fullRelation half quarter a b c kappa tau z
      (maskWeights271 half semanticZ) true q 0 +
    fullRelation half quarter a b c kappa tau z
      (maskWeights271 half semanticZ) true q 4 =
      quarter * (∑ d : Fin 256, ∑ s : Fin 4,
        q (d,s) * fullWeight half a b c kappa tau z
          (maskWeights271 half semanticZ) true (d,s)) at hcoeff
  rw [hboundary] at hcoeff
  exact (mul_eq_zero.mp hcoeff.symm).resolve_left hquarter

#print axioms semantic_structured_moment
end
end AspisV8R19.R863SemanticStructuredMoment
