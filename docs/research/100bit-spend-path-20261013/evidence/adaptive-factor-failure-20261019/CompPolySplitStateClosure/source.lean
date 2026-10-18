import CompPolySplitFactorQuality
import FiniteFieldNormalizedRootFactor

noncomputable section
namespace AspisR1.CompPolySplitStateClosure
open CompPoly Polynomial AspisR1.CompPolySplitFactorQuality
variable {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

/-- State invariant needed to apply the per-node split probability bound. -/
def SplitState (f : CPolynomial K) : Prop :=
  f.toPoly.Monic ∧ f.toPoly.Splits ∧ f.toPoly.Separable

theorem two_distinct_roots (f : CPolynomial K) (hf : SplitState f)
    (hdeg : 1 < f.toPoly.natDegree) :
    ∃ a b : K, a ≠ b ∧ IsRoot f.toPoly a ∧ IsRoot f.toPoly b := by
  have hn := Polynomial.nodup_roots hf.2.2
  have hcard : 1 < f.toPoly.roots.toFinset.card := by
    rw [Multiset.card_toFinset, Multiset.dedup_eq_self.mpr hn]
    rw [← hf.2.1.natDegree_eq_card_roots]
    exact hdeg
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  exact ⟨a, b, hab,
    (Polynomial.mem_roots hf.1.ne_zero).mp (Multiset.mem_toFinset.mp ha),
    (Polynomial.mem_roots hf.1.ne_zero).mp (Multiset.mem_toFinset.mp hb)⟩

theorem retry_children_state (f d : CPolynomial K) (q t : Nat)
    (coins : Fin t → K × K) (hf : SplitState f)
    (hs : CompPolySplitRetries.retry f q t coins = some d) :
    SplitState d ∧ SplitState (f.divByMonic d) := by
  have hd := retry_quality f d q t coins hf.1 hs
  have hc := complement_quality f d hf.1 hd.1 hd.2
  dsimp only at hc
  have hediv : (f.divByMonic d).toPoly ∣ f.toPoly := by
    exact ⟨d.toPoly, hc.1.symm.trans (mul_comm _ _)⟩
  constructor
  · exact ⟨hd.1, hf.2.1.of_dvd hf.1.ne_zero hd.2.1, hf.2.2.of_dvd hd.2.1⟩
  · exact ⟨hc.2.1, hf.2.1.of_dvd hf.1.ne_zero hediv, hf.2.2.of_dvd hediv⟩

#print axioms two_distinct_roots
#print axioms retry_children_state
end AspisR1.CompPolySplitStateClosure
