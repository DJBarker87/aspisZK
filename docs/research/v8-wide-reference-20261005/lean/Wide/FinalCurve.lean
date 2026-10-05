import Wide.FinalCurveBranch

/-!
# Exact final V7 fixed-curve extraction
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
open AspisWide.FinalEncoder
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6PublishedTheoremInterfaces
open AspisCircleGroupOrder (P)

noncomputable section

private theorem exists_four_elim
    {A B C D : Type*} {P : A → B → C → D → Prop} {Q : Prop}
    (existsWitness : ∃ a b c d, P a b c d)
    (finish : ∀ a b c d, P a b c d → Q) : Q := by
  obtain ⟨a, b, c, d, property⟩ := existsWitness
  exact finish a b c d property

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
set_option linter.constructorNameAsVariable false in
/-- Extract a released-message curve from one fixed exact symbolic
interpolant and an explicitly supplied set of valid challenges. -/
theorem exists_exactV7Final_curve_of_interpolant
    (lanes : Fin 4 → FinalWord E)
    (strategy : ProximateStrategy E (Fin 262144)
      (FinalMessage E))
    (coefficients :
      CurveMonomialIndex 255 3 finalCurveXBound finalCurveYRows
        finalCurveZBound → E)
    (coefficientsNeZero : coefficients ≠ 0)
    (kernel : curveInterpolationMap (exactFinalGRSConversion (K := E)).points
      lanes coefficients = 0)
    (challenges : Finset E)
    (validOn : ∀ gamma ∈ challenges,
      ValidResponse exactFinalEncoder 9557 lanes strategy gamma)
    (outerMany :
      finalCurveZBound + 224 * finalCurveYRows * finalCurveZBound +
          58 * (255 + 1) * finalCurveYRows ^ 2 * finalCurveZBound +
            (3 * 262144 + 1) * finalCurveYRows < challenges.card) :
    ∃ (components : Fin 4 → FinalMessage E)
        (selected : Finset E),
      selected ⊆ challenges ∧
      3 * Fintype.card (Fin 262144) < selected.card ∧
      ∀ gamma ∈ selected,
        CandidateOnCurve exactFinalEncoder strategy components
          gamma := by
  apply exists_four_elim
    (exists_exactV7Final_weighted_fixed_branch lanes strategy coefficients
      coefficientsNeZero kernel challenges validOn outerMany)
  intro globalFactor x₀ localFactor selected specification
  obtain ⟨componentMessages, selectedLarge, onCurve⟩ :=
    exists_exactV7Final_components_of_selected_branch lanes strategy
      challenges validOn globalFactor x₀ localFactor selected
      specification.2.1 specification.2.2.1 specification.2.2.2.1
      specification.2.2.2.2.1 specification.2.2.2.2.2.1
      specification.2.2.2.2.2.2.1 specification.2.2.2.2.2.2.2
  exact ⟨componentMessages, selected,
    specification.2.2.2.2.2.2.1, selectedLarge, onCurve⟩

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 300000 in
/-- The mathematical degree-three extraction step over any explicitly supplied
finite set of valid challenges.  Its conclusion already consists of released
V7 messages, which keeps the concrete `goodChallenges` predicate out of the
branch/Hensel proof term. -/
theorem exists_exactV7Final_curve_of_valid_challenges
    (lanes : Fin 4 → FinalWord E)
    (strategy : ProximateStrategy E (Fin 262144)
      (FinalMessage E))
    (challenges : Finset E)
    (validOn : ∀ gamma ∈ challenges,
      ValidResponse exactFinalEncoder 9557 lanes strategy gamma)
    (outerMany :
      finalCurveZBound + 224 * finalCurveYRows * finalCurveZBound +
          58 * (255 + 1) * finalCurveYRows ^ 2 * finalCurveZBound +
            (3 * 262144 + 1) * finalCurveYRows < challenges.card) :
    ∃ (components : Fin 4 → FinalMessage E)
        (selected : Finset E),
      selected ⊆ challenges ∧
      3 * Fintype.card (Fin 262144) < selected.card ∧
      ∀ gamma ∈ selected,
        CandidateOnCurve exactFinalEncoder strategy components
          gamma := by
  obtain ⟨coefficients, coefficientsNeZero, kernel⟩ :=
    exists_exactFinalCurveInterpolation lanes
  exact exists_exactV7Final_curve_of_interpolant lanes strategy coefficients
    coefficientsNeZero kernel challenges validOn outerMany

#print axioms exists_exactV7Final_curve_of_interpolant
#print axioms exists_exactV7Final_curve_of_valid_challenges

end

end AspisWide.Terminal
