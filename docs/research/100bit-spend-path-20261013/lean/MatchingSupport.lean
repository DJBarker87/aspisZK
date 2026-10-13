import R1ConcreteBinding
import AspisFormal.V5WithoutReplacementQuerySoundness

/-! Support-cardinality factoring for the existing deterministic binding
theorem. The final probability statement is only for the separately defined
ideal ordered-injection sampler; this module makes no claim about an actual
query sampler, random-oracle law, work factor, or protocol security. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.MatchingSupport

open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriDegreeThreeCorrelatedAgreement
open Polynomial

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

abbrev InitialWord (K : Type) := AspisPool.AlgorithmicCircleDecoderV7.InitialWord K
abbrev FinalWord (K : Type) := AspisPool.AlgorithmicCircleDecoderV7.FinalWord K
abbrev Functional (K : Type) [Field K] := (Fin 1024 → K) →ₗ[K] K
abbrev SmallMessage (K : Type) := AspisR1.ConcreteProjection.SmallMessage K

/-- The fixed statement-like data used by the deterministic two-fold binding
implication. All equations are supplied separately through `Good` and
`AcceptedPairing`. -/
structure Data (E : Type) [Field E] [Fintype E] [DecidableEq E]
    [Algebra (ZMod P) E] where
  W : Fin 29 → InitialWord E
  V : FinalWord E
  F : Fin 6 → Functional E
  F0 : Functional E
  Y : Fin 6 → Fin 29 → E
  c0 : E
  gamma : E
  kappa : E
  alpha0 : E
  alpha1 : E
  p0 : E[X]
  p1 : E[X]
  f : SmallMessage E

def match0 (d : Data E) (i : Fin 262144) : Prop :=
  AspisR1.FirstFold.foldWord d.alpha0
    (AspisR1.TwoFoldExtraction.batchedWord d.W d.gamma) i = d.V i

def match1 (d : Data E) (i : Fin 262144) : Prop :=
  curveValue (AspisR1.SecondFoldRestoration.channels d.V) d.alpha1
      (AspisR1.parentIndex i) =
    AspisR1.ConcreteProjection.secondEncoder d.f (AspisR1.parentIndex i)

/-- Full original-position matching support for the two equations. -/
def matchingSet (d : Data E) : Finset (Fin 262144) :=
  by classical exact Finset.univ.filter (fun i => match0 d i ∧ match1 d i)

/-- The exact literal-candidate and functional conclusion of deterministic
binding. -/
def Claims (d : Data E) : Prop :=
  ∃ t ∈ AspisR1.ConcreteBinding.candidates d.W,
    (∀ j : Fin 6, ∀ l : Fin 29, d.F j (t l) = d.Y j l) ∧
      d.F0 (AspisR1.ConcreteBinding.batches d.gamma t) = d.c0

/-- The nonzero challenge condition and precisely the four bad-set
exclusions already consumed by `ConcreteBinding.binding`. -/
def Good (d : Data E) : Prop :=
  d.gamma ≠ 0 ∧
  d.gamma ∉ AspisR1.ConcreteBinding.gammaBad d.W d.F d.Y ∧
  d.kappa ∉ AspisR1.ConcreteBinding.kappaBad d.W d.F d.F0 d.Y d.c0 d.gamma ∧
  d.alpha0 ∉ AspisR1.ConcreteBinding.firstBad d.W d.gamma
    (AspisR1.FunctionalWeights.weights d.F d.F0 d.kappa) d.p0 ∧
  d.alpha1 ∉ AspisR1.ConcreteBinding.secondBad d.W d.V d.gamma d.alpha0
    (AspisR1.FunctionalWeights.weights d.F d.F0 d.kappa) d.p1

/-- The exact final dot-product check and two boundary equations required by
the deterministic pairing theorem. -/
def AcceptedPairing (d : Data E) : Prop :=
  d.p1.eval d.alpha1 = AspisR1.RoundPairing.dot d.f
    (AspisR1.RoundPairing.dualFold (n := 64) d.alpha1
      (AspisR1.RoundPairing.dualFold (n := 256) d.alpha0
        (AspisR1.FunctionalWeights.weights d.F d.F0 d.kappa))) ∧
  AspisR1.TwoRoundComparison.boundary d.p1 =
    AspisR1.RoundPairing.quarter * d.p0.eval d.alpha0 ∧
  AspisR1.TwoRoundComparison.boundary d.p0 =
    AspisR1.RoundPairing.quarter *
      AspisR1.JointFunctionalBinding.claimedValue d.Y d.c0 d.gamma d.kappa

set_option maxRecDepth 4096 in
/-- At 9558 matching original positions, the existing concrete binding
theorem yields a tuple in the literal committed-word list with all six
functional claims and the constant claim. -/
theorem large_matching_implies_claims (d : Data E)
    (hgood : Good d) (haccepted : AcceptedPairing d)
    (hcard : 9558 ≤ (matchingSet d).card) : Claims d := by
  classical
  rcases hgood with ⟨hgamma_ne, hgamma, hkappa, hfirst, hsecond⟩
  rcases haccepted with ⟨hfinal, hboundary1, hboundary0⟩
  have hmatch0 : ∀ i ∈ matchingSet d,
      AspisR1.FirstFold.foldWord d.alpha0
        (AspisR1.TwoFoldExtraction.batchedWord d.W d.gamma) i = d.V i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.1
  have hmatch1 : ∀ i ∈ matchingSet d,
      curveValue (AspisR1.SecondFoldRestoration.channels d.V) d.alpha1
          (AspisR1.parentIndex i) =
        AspisR1.ConcreteProjection.secondEncoder d.f (AspisR1.parentIndex i) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.2
  have hb := AspisR1.ConcreteBinding.binding d.W d.V d.F d.F0 d.Y d.c0
    d.gamma d.kappa d.alpha0 d.alpha1 d.p0 d.p1 d.f
    hgamma_ne hgamma hkappa hfirst hsecond (matchingSet d) hcard
    hmatch0 hmatch1 hfinal hboundary1 hboundary0
  exact hb

/-- If the deterministic claims fail under the listed premises, the support
has at most 9557 matching original positions. -/
theorem no_claims_card_le (d : Data E)
    (hgood : Good d) (haccepted : AcceptedPairing d)
    (hnot : ¬ Claims d) : (matchingSet d).card ≤ 9557 := by
  by_contra hlarge
  have hcard : 9558 ≤ (matchingSet d).card := by omega
  exact hnot (large_matching_implies_claims d hgood haccepted hcard)

/-- Ideal ordered-injection miss bound for 22 queries, conditional on the
deterministic no-claims support bound. This is not a theorem about the
deployed sampler or its challenge distribution. -/
theorem no_claims_ideal_q22_bound (d : Data E)
    (hgood : Good d) (haccepted : AcceptedPairing d)
    (hnot : ¬ Claims d) :
    AspisV5WithoutReplacementQuerySoundness.idealMissProbability
        (q := 22) (matchingSet d) ≤
      ((9557 : Nat).descFactorial 22 : ℝ) /
        (262144 : Nat).descFactorial 22 := by
  apply AspisV5WithoutReplacementQuerySoundness.ideal_miss_probability_mono_card
  · exact no_claims_card_le d hgood haccepted hnot
  · omega

#print axioms large_matching_implies_claims
#print axioms no_claims_card_le
#print axioms no_claims_ideal_q22_bound

end AspisR1.MatchingSupport
end
