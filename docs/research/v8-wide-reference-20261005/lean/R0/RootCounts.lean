import Mathlib.Tactic

/-! Root unions for the opening-layer exceptional sets. Zero polynomials
contribute no roots: only false polynomial identities are bad events. -/
set_option autoImplicit false
namespace AspisR0.RootCounts
open Polynomial
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

def badRoots (p : K[X]) : Finset K := by
  classical
  exact Finset.univ.filter (fun x => p ≠ 0 ∧ p.eval x = 0)

@[simp] theorem mem_badRoots (p : K[X]) (x : K) :
    x ∈ badRoots p ↔ p ≠ 0 ∧ p.eval x = 0 := by simp [badRoots]

theorem badRoots_card (p : K[X]) : (badRoots p).card ≤ p.natDegree := by
  by_contra h
  have hp := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p (badRoots p)
    (fun x hx => (mem_badRoots p x).mp hx |>.2) (Nat.lt_of_not_ge h)
  simp [badRoots, hp] at h

theorem union_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → K[X]) (d : Nat) (hd : ∀ i ∈ s, (p i).natDegree ≤ d) :
    (s.biUnion (fun i => badRoots (p i))).card ≤ s.card*d := by
  calc
    _ ≤ ∑ i ∈ s, (badRoots (p i)).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ s, d := Finset.sum_le_sum fun i hi => (badRoots_card (p i)).trans (hd i hi)
    _ = _ := by simp

#print axioms badRoots_card
#print axioms union_bound
end
end AspisR0.RootCounts
