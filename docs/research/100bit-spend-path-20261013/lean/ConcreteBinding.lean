import R1TwoFoldExtraction
import R1TwoRoundPairing
import R1FunctionalWeights

/-! Deterministic binding of the two-fold opening to one tuple in the literal
committed-word list. All functional weights are derived from linear maps;
there is no candidate-uniqueness premise. Matching support, accepted field
equations and bad-set exclusions are explicit inputs. This is not a Rust,
Merkle, probability, semantic-relation, or Fiat--Shamir theorem. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.ConcreteBinding

open Polynomial
open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.Agreement

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

abbrev Tuple (K : Type) := Fin 29 → InitialMessage K
abbrev Functional (K : Type) [Field K] := (Fin 1024 → K) →ₗ[K] K

def candidates (W : Fin 29 → InitialWord K) : Finset (Tuple K) :=
  AspisR1.InitialResponses.Lambda W

def batches (gamma : K) : Tuple K → Fin 1024 → K :=
  fun t => exactInitialMessageCurve t gamma

def gammaBad (W : Fin 29 → InitialWord K)
    (F : Fin 6 → Functional K) (Y : Fin 6 → Fin 29 → K) : Finset K :=
  AspisR1.InitialResponses.B1 W ∪
    AspisR1.JointFunctionalBinding.gammaBad (candidates W) id F Y

def kappaBad (W : Fin 29 → InitialWord K)
    (F : Fin 6 → Functional K) (F0 : Functional K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma : K) : Finset K :=
  AspisR1.JointFunctionalBinding.kappaBad (candidates W) id F F0 Y c0 gamma

def firstBad (W : Fin 29 → InitialWord K) (gamma : K)
    (w : Fin 1024 → K) (p0 : K[X]) : Finset K :=
  AspisR1.FinalResponses.B6
      (AspisR1.FirstFold.channels (AspisR1.TwoFoldExtraction.batchedWord W gamma)) ∪
    AspisR1.TwoRoundComparison.comparisonBad (candidates W) p0
      (AspisR1.TwoRoundPairing.round0Truth (n := 64) (batches gamma) w)

def secondBad (W : Fin 29 → InitialWord K) (V : FinalWord K)
    (gamma alpha0 : K) (w : Fin 1024 → K) (p1 : K[X]) : Finset K :=
  AspisR1.SecondFoldMatched.secondBad (AspisR1.SecondFoldRestoration.channels V) ∪
    AspisR1.TwoRoundComparison.comparisonBad (candidates W) p1
      (AspisR1.TwoRoundPairing.round1Truth (n := 64) alpha0 (batches gamma) w)

theorem candidates_card (W : Fin 29 → InitialWord K) :
    (candidates W).card ≤ 100 := AspisR1.InitialResponses.Lambda_card W

theorem gammaBad_card (W : Fin 29 → InitialWord K)
    (F : Fin 6 → Functional K) (Y : Fin 6 → Fin 29 → K) :
    (gammaBad W F Y).card ≤ 336869026622539 := by
  have h0 := AspisR1.InitialResponses.B1_card W
  have h1 := AspisR1.JointFunctionalBinding.gamma_bad_card_le_16800
    (candidates W) id F Y (candidates_card W)
  unfold gammaBad
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add h0 h1)

theorem kappaBad_card (W : Fin 29 → InitialWord K)
    (F : Fin 6 → Functional K) (F0 : Functional K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma : K) :
    (kappaBad W F F0 Y c0 gamma).card ≤ 600 :=
  AspisR1.JointFunctionalBinding.kappa_bad_card_le_600
    (candidates W) id F F0 Y c0 gamma (candidates_card W)

theorem firstBad_card (W : Fin 29 → InitialWord K) (gamma : K)
    (w : Fin 1024 → K) (p0 : K[X]) (hdegree : p0.natDegree ≤ 6) :
    (firstBad W gamma w p0).card ≤ 9396508281846 := by
  have h0 := AspisR1.FinalResponses.B6_card
    (AspisR1.FirstFold.channels (AspisR1.TwoFoldExtraction.batchedWord W gamma))
  have h1 := AspisR1.TwoRoundPairing.round0_bad_card_le_600 (n := 64)
    (candidates W) p0 (batches gamma) w (candidates_card W) hdegree
  unfold firstBad
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add h0 h1)

theorem secondBad_card (W : Fin 29 → InitialWord K) (V : FinalWord K)
    (gamma alpha0 : K) (w : Fin 1024 → K) (p1 : K[X])
    (hdegree : p1.natDegree ≤ 6) :
    (secondBad W V gamma alpha0 w p1).card ≤ 9396508281846 := by
  have h0 := AspisR1.SecondFoldMatched.secondBad_card
    (AspisR1.SecondFoldRestoration.channels V)
  have h1 := AspisR1.TwoRoundPairing.round1_bad_card_le_600 (n := 64)
    (candidates W) p1 alpha0 (batches gamma) w (candidates_card W) hdegree
  unfold secondBad
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add h0 h1)

set_option maxRecDepth 4096 in
/-- Concrete algebraic binding outside the explicitly counted bad sets. -/
theorem binding
    (W : Fin 29 → InitialWord K) (V : FinalWord K)
    (F : Fin 6 → Functional K) (F0 : Functional K)
    (Y : Fin 6 → Fin 29 → K) (c0 gamma kappa alpha0 alpha1 : K)
    (p0 p1 : K[X]) (f : AspisR1.ConcreteProjection.SmallMessage K)
    (hgamma_ne : gamma ≠ 0)
    (hgamma : gamma ∉ gammaBad W F Y)
    (hkappa : kappa ∉ kappaBad W F F0 Y c0 gamma)
    (hfirst : alpha0 ∉ firstBad W gamma
      (AspisR1.FunctionalWeights.weights F F0 kappa) p0)
    (hsecond : alpha1 ∉ secondBad W V gamma alpha0
      (AspisR1.FunctionalWeights.weights F F0 kappa) p1)
    (M : Finset (Fin 262144)) (hM : 9558 ≤ M.card)
    (hmatch0 : ∀ i ∈ M,
      AspisR1.FirstFold.foldWord alpha0
        (AspisR1.TwoFoldExtraction.batchedWord W gamma) i = V i)
    (hmatch1 : ∀ i ∈ M,
      AspisV5FriDegreeThreeCorrelatedAgreement.curveValue
          (AspisR1.SecondFoldRestoration.channels V) alpha1
          (AspisR1.parentIndex i) =
        AspisR1.ConcreteProjection.secondEncoder f (AspisR1.parentIndex i))
    (hfinal : p1.eval alpha1 = AspisR1.RoundPairing.dot f
      (AspisR1.RoundPairing.dualFold (n := 64) alpha1
        (AspisR1.RoundPairing.dualFold (n := 256) alpha0
          (AspisR1.FunctionalWeights.weights F F0 kappa))))
    (hboundary1 : AspisR1.TwoRoundComparison.boundary p1 =
      AspisR1.RoundPairing.quarter * p0.eval alpha0)
    (hboundary0 : AspisR1.TwoRoundComparison.boundary p0 =
      AspisR1.RoundPairing.quarter *
        AspisR1.JointFunctionalBinding.claimedValue Y c0 gamma kappa) :
    ∃ t ∈ candidates W,
      (∀ j : Fin 6, ∀ l : Fin 29, F j (t l) = Y j l) ∧
      F0 (exactInitialMessageCurve t gamma) = c0 := by
  have hg := hgamma
  have ha0 := hfirst
  have ha1 := hsecond
  simp only [gammaBad, Finset.mem_union, not_or] at hg
  simp only [firstBad, Finset.mem_union, not_or] at ha0
  simp only [secondBad, Finset.mem_union, not_or] at ha1
  obtain ⟨t, ht, hextract⟩ := AspisR1.TwoFoldExtraction.two_fold_extract
    W V gamma alpha0 alpha1 hgamma_ne hg.1 ha0.1 ha1.1 f M hM hmatch0 hmatch1
  have hpair := AspisR1.TwoRoundPairing.two_round_pairing (n := 64)
    AspisR1.ConcreteProjection.four_ne_zero (candidates W) (batches gamma)
    (AspisR1.FunctionalWeights.weights F F0 kappa) t ht p0 p1 alpha0 alpha1
    (AspisR1.JointFunctionalBinding.claimedValue Y c0 gamma kappa) f
    ha0.2 ha1.2 hextract hfinal hboundary1 hboundary0
  have haccepted : AspisR1.JointFunctionalBinding.weightedValue
      id F F0 t gamma kappa =
        AspisR1.JointFunctionalBinding.claimedValue Y c0 gamma kappa := by
    have hp := hpair.2.2.symm
    rw [AspisR1.FunctionalWeights.dot_weights] at hp
    exact hp
  have hclaims := AspisR1.JointFunctionalBinding.joint_functional_binding
    (candidates W) id F F0 Y c0 t ht gamma kappa hg.2 hkappa haccepted
  exact ⟨t, ht, hclaims⟩

#print axioms candidates_card
#print axioms gammaBad_card
#print axioms kappaBad_card
#print axioms firstBad_card
#print axioms secondBad_card
#print axioms binding
end AspisR1.ConcreteBinding
end
