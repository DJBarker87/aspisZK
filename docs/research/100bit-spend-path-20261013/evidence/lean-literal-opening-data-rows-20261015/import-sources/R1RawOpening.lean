import R1RawPairing
import R1MatchingSupport

/-! Bridge the existing deterministic opening interface to an arbitrary seven
raw-row coefficient matrix. The statements are coefficient algebra only: they
do not identify the rows with Rust constructors or close source/security gates. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawOpening

open scoped BigOperators
open AspisCircleGroupOrder
variable {K E : Type} [Field K] [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

def withRows (iota : K →+* E) (raw : Fin 7 → Fin 1024 → K)
    (d : AspisR1.MatchingSupport.Data E) :
    AspisR1.MatchingSupport.Data E :=
  { d with
    F := AspisR1.RawFunctionalWeights.rawFunctionals (n := 1024) iota raw
    F0 := AspisR1.RawFunctionalWeights.rawBaseFunctional (n := 1024) iota raw }

def rawClaims (iota : K →+* E) (raw : Fin 7 → Fin 1024 → K)
    (d : AspisR1.MatchingSupport.Data E) : Prop :=
  ∃ t ∈ AspisR1.ConcreteBinding.candidates d.W,
    (∀ j : Fin 6, ∀ l : Fin 29,
      (∑ i : Fin 1024,
        t l i * iota (raw ⟨j.val + 1, by omega⟩ i)) = d.Y j l) ∧
    (∑ i : Fin 1024,
      AspisR1.ConcreteBinding.batches d.gamma t i * iota (raw 0 i)) = d.c0

def rawAcceptedPairing (iota : K →+* E) (raw : Fin 7 → Fin 1024 → K)
    (d : AspisR1.MatchingSupport.Data E) : Prop :=
  d.p1.eval d.alpha1 =
      ∑ k : Fin 7, d.kappa ^ k.val *
        AspisR1.RoundPairing.dot d.f
          (AspisR1.RoundPairing.dualFold d.alpha1
            (AspisR1.RoundPairing.dualFold d.alpha0
              (AspisR1.RawPairing.embeddedRow (n := 1024) iota (raw k)))) ∧
  AspisR1.TwoRoundComparison.boundary d.p1 =
    AspisR1.RoundPairing.quarter * d.p0.eval d.alpha0 ∧
  AspisR1.TwoRoundComparison.boundary d.p0 =
    AspisR1.RoundPairing.quarter *
      AspisR1.JointFunctionalBinding.claimedValue d.Y d.c0 d.gamma d.kappa

set_option maxRecDepth 4096 in
theorem claims_iff_raw (iota : K →+* E) (raw : Fin 7 → Fin 1024 → K)
    (d : AspisR1.MatchingSupport.Data E) :
    AspisR1.MatchingSupport.Claims (withRows iota raw d) ↔ rawClaims iota raw d := by
  change
    (∃ t ∈ AspisR1.ConcreteBinding.candidates d.W,
      (∀ j : Fin 6, ∀ l : Fin 29,
        AspisR1.RawFunctionalWeights.rowMap iota
            (raw ⟨j.val + 1, by omega⟩) (t l) = d.Y j l) ∧
      AspisR1.RawFunctionalWeights.rowMap iota (raw 0)
        (AspisR1.ConcreteBinding.batches d.gamma t) = d.c0) ↔ rawClaims iota raw d
  constructor
  · rintro ⟨t, ht, hrows, hbase⟩
    refine ⟨t, ht, ?_, ?_⟩
    · intro j l
      simpa [AspisR1.RawFunctionalWeights.rowMap] using hrows j l
    · simpa [AspisR1.RawFunctionalWeights.rowMap] using hbase
  · rintro ⟨t, ht, hrows, hbase⟩
    refine ⟨t, ht, ?_, ?_⟩
    · intro j l
      simpa [AspisR1.RawFunctionalWeights.rowMap] using hrows j l
    · simpa [AspisR1.RawFunctionalWeights.rowMap] using hbase

set_option maxRecDepth 4096 in
theorem accepted_pairing_iff_raw (iota : K →+* E)
    (raw : Fin 7 → Fin 1024 → K) (d : AspisR1.MatchingSupport.Data E) :
    AspisR1.MatchingSupport.AcceptedPairing (withRows iota raw d) ↔
      rawAcceptedPairing iota raw d := by
  constructor
  · rintro ⟨hfinal, hboundary1, hboundary0⟩
    simp only [withRows] at hfinal hboundary1 hboundary0
    rw [AspisR1.RawPairing.two_dual_dot_eq_seven_rows] at hfinal
    exact ⟨hfinal, hboundary1, hboundary0⟩
  · rintro ⟨hfinal, hboundary1, hboundary0⟩
    simp only [AspisR1.MatchingSupport.AcceptedPairing, withRows]
    have hdot : d.p1.eval d.alpha1 =
        AspisR1.RoundPairing.dot d.f
          (AspisR1.RoundPairing.dualFold d.alpha1
            (AspisR1.RoundPairing.dualFold d.alpha0
              (AspisR1.FunctionalWeights.weights
                (AspisR1.RawFunctionalWeights.rawFunctionals (n := 1024) iota raw)
                (AspisR1.RawFunctionalWeights.rawBaseFunctional (n := 1024) iota raw)
                d.kappa))) := by
      rw [AspisR1.RawPairing.two_dual_dot_eq_seven_rows]
      exact hfinal
    exact ⟨hdot, hboundary1, hboundary0⟩

set_option maxRecDepth 4096 in
theorem large_matching_implies_raw_claims (iota : K →+* E)
    (raw : Fin 7 → Fin 1024 → K) (d : AspisR1.MatchingSupport.Data E)
    (hgood : AspisR1.MatchingSupport.Good (withRows iota raw d))
    (haccepted : AspisR1.MatchingSupport.AcceptedPairing (withRows iota raw d))
    (hcard : 9558 ≤
      (AspisR1.MatchingSupport.matchingSet (withRows iota raw d)).card) :
    rawClaims iota raw d := by
  apply (claims_iff_raw iota raw d).mp
  exact AspisR1.MatchingSupport.large_matching_implies_claims
    (withRows iota raw d) hgood haccepted hcard

#print axioms claims_iff_raw
#print axioms accepted_pairing_iff_raw
#print axioms large_matching_implies_raw_claims
end AspisR1.RawOpening
end
