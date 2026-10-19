import Wide.InitialCurve

/-!
# Exact initial V7 width-29 correlated agreement

The initial instance is separated from the final instance so direct kernel
replay does not retain both large dependent interpolation environments at once.
-/

set_option autoImplicit false
set_option maxRecDepth 262144

namespace AspisWide.Terminal

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]


open Polynomial
open AspisWide.Agreement
open AspisWide.Interpolation
open AspisWide.Factors
open AspisWide.LocalFactors
open AspisWide.Smooth
open AspisWide.FunctionField
open AspisWide.PowerSeriesLift
open AspisWide.RegularHensel
open AspisWide.FactorBudgets
open AspisWide.ConcreteBranch
open AspisWide.OuterSelection
open AspisWide.GRSConversion
open AspisWide.FinalEncoder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6Width29CorrelatedAgreement
open AspisV6PublishedTheoremInterfaces
open AspisCircleGroupOrder (P)

noncomputable section




set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
/-- The exact released initial V7 `1024 → 2^20` encoder satisfies the complete
width-29 curve-decodability predicate at the unchanged release cap. -/
theorem exactV7InitialWidth29CurveDecodable :
    Width29CurveDecodable (exactInitialEncoder (K := E)) 38229
      initialBatchChallengeCap := by
  classical
  intro lanes strategy manyGood
  obtain ⟨challenges, challengesEq, validOn⟩ :=
    packageWidth29GoodChallenges exactInitialEncoder 38229 lanes strategy
  have validExact : ∀ gamma ∈ challenges,
      Width29ValidResponse exactInitialEncoder 38229 lanes strategy gamma := by
    intro gamma gammaMem
    exact (validOn gamma gammaMem).2
  have outerMany :
      initialCurveZBound + 224 * initialCurveYRows * initialCurveZBound +
          58 * (1024 + 1) * initialCurveYRows ^ 2 * initialCurveZBound +
            (28 * 1048576 + 1) * initialCurveYRows < challenges.card := by
    apply lt_trans (b := initialBatchChallengeCap)
    · norm_num [initialCurveZBound, initialCurveYRows,
        initialBatchChallengeCap]
    · rw [challengesEq]
      exact manyGood
  obtain ⟨components, selected, selectedSubset, selectedLarge, onCurve⟩ :=
    exists_exactV7Initial_curve_of_valid_challenges lanes strategy challenges
      validExact outerMany
  refine ⟨components, selected, ?_, selectedLarge, onCurve⟩
  intro gamma gammaMem
  rw [← challengesEq]
  exact selectedSubset gammaMem

/-- V7-specific discharge of the historical published initial interface. -/
theorem exactV7InitialPublishedWidth29CurveDecodability :
    PublishedInitialWidth29CurveDecodability (exactInitialEncoder (K := E)) := by
  change Width29CurveDecodable (exactInitialEncoder (K := E)) 38229
    initialBatchChallengeCap
  exact exactV7InitialWidth29CurveDecodable

#print axioms exactV7InitialWidth29CurveDecodable
#print axioms exactV7InitialPublishedWidth29CurveDecodability


end

end AspisWide.Terminal
