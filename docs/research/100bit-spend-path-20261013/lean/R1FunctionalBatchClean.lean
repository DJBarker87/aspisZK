import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card

/-! Finite-family polynomial root counting for a direct joint-list binding.

This file proves only a finite root-union bound and its pointwise outside
consequence. It introduces no uniqueness premise or protocol-security claim. -/

set_option autoImplicit false

noncomputable section

namespace AspisR1

open Polynomial

variable {K T : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Candidate values where at least one nonzero family polynomial vanishes. -/
def functionalBadRoots (ts : Finset T) (polys : T → K[X]) : Finset K :=
  ts.biUnion (fun t =>
    if polys t = 0 then ∅ else
      Finset.univ.filter (fun x : K => (polys t).eval x = 0))

/-- The union of the nonzero members' root sets costs at most the sum of
their degree bounds. -/
theorem functional_bad_roots_card_le
    (ts : Finset T) (polys : T → K[X]) (degreeBound : Nat)
    (hdegree : ∀ t ∈ ts, (polys t).natDegree ≤ degreeBound) :
    (functionalBadRoots ts polys).card ≤ ts.card * degreeBound := by
  classical
  calc
    (functionalBadRoots ts polys).card ≤
        ∑ t ∈ ts, (if polys t = 0 then ∅ else
          Finset.univ.filter (fun x : K => (polys t).eval x = 0)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ ts, degreeBound := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hp : polys t = 0
      · simp [hp]
      · have hsubset :
            (Finset.univ.filter (fun x : K => (polys t).eval x = 0)) ⊆
              (polys t).roots.toFinset := by
          intro x hx
          rw [Finset.mem_filter] at hx
          rw [Multiset.mem_toFinset, (polys t).mem_roots hp]
          exact hx.2
        calc
          (if polys t = 0 then ∅ else
              Finset.univ.filter (fun x : K => (polys t).eval x = 0)).card
              = (Finset.univ.filter (fun x : K => (polys t).eval x = 0)).card := by
                  simp [hp]
          _ ≤ (polys t).roots.toFinset.card := Finset.card_le_card hsubset
          _ ≤ (polys t).roots.card := Multiset.toFinset_card_le _
          _ ≤ (polys t).natDegree := (polys t).card_roots'
          _ ≤ degreeBound := hdegree t ht
    _ = ts.card * degreeBound := by simp

#print axioms functional_bad_roots_card_le

/-- A zero of an in-family polynomial outside the bad union forces that
polynomial to be identically zero. -/
theorem eval_zero_outside_functional_bad_roots
    (ts : Finset T) (polys : T → K[X]) (x : K)
    (hout : x ∉ functionalBadRoots ts polys)
    (t : T) (ht : t ∈ ts) (heval : (polys t).eval x = 0) :
    polys t = 0 := by
  classical
  by_contra hp
  have hx : x ∈ (if polys t = 0 then ∅ else
      Finset.univ.filter (fun y : K => (polys t).eval y = 0)) := by
    simp [hp, heval]
  exact hout (Finset.mem_biUnion.mpr ⟨t, ht, hx⟩)

#print axioms eval_zero_outside_functional_bad_roots

/-- At most 100 candidates, each of degree at most 6, give a 600-element
root union bound. -/
theorem functional_bad_roots_card_le_600
    (ts : Finset T) (polys : T → K[X])
    (hts : ts.card ≤ 100)
    (hdegree : ∀ t ∈ ts, (polys t).natDegree ≤ 6) :
    (functionalBadRoots ts polys).card ≤ 600 := by
  calc
    (functionalBadRoots ts polys).card ≤ ts.card * 6 :=
      functional_bad_roots_card_le ts polys 6 hdegree
    _ ≤ 100 * 6 := by nlinarith [hts]
    _ = 600 := by norm_num

#print axioms functional_bad_roots_card_le_600

/-- A family of at most 600 candidates, each of degree at most 28, gives a
16,800-element root union bound. -/
theorem functional_bad_roots_card_le_16800
    (ts : Finset T) (polys : T → K[X])
    (hts : ts.card ≤ 600)
    (hdegree : ∀ t ∈ ts, (polys t).natDegree ≤ 28) :
    (functionalBadRoots ts polys).card ≤ 16800 := by
  calc
    (functionalBadRoots ts polys).card ≤ ts.card * 28 :=
      functional_bad_roots_card_le ts polys 28 hdegree
    _ ≤ 600 * 28 := by nlinarith [hts]
    _ = 16800 := by norm_num

#print axioms functional_bad_roots_card_le_16800

end AspisR1

end
