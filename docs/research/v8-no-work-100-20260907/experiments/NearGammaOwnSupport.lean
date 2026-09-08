import NearGammaCover
import JointImageGame
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Own-support recovery for the curve constructed from 29 nodes. This does
not require its support to equal any one gamma-combination support. -/
set_option autoImplicit false
namespace AspisV8.NearGammaOwnSupport
open Polynomial Finset
open AspisV8.NearGammaCover AspisV8.JointImageGame

variable {K Pos Slot : Type*} [Field K] [DecidableEq K] [DecidableEq Pos]
  [Fintype Slot] [DecidableEq Slot] [DecidableEq (Slot → K)]

theorem own_support_64_29 (D : Finset Pos) (S I : Finset K)
    (v : Pos → Slot → K[X]) (cand : K → Pos → Slot → K)
    (hD : D.card = 262144) (hS : S.card = 64) (hI : I.card = 29)
    (degree : ∀ x y, (v x y).degree < 29)
    (near : ∀ g ∈ S,
      (D.filter fun x => (fun y => (v x y).eval g) ≠ cand g x).card ≤ 9301)
    (candEq : ∀ g ∈ S,
      cand g = fun x y => (interp I cand x y).eval g) :
    245609 ≤ (D.filter fun x => ∀ y, v x y = interp I cand x y).card := by
  classical
  let Bad := D.filter fun x => ¬ ∀ y, v x y = interp I cand x y
  have badRoots : ∀ x ∈ Bad,
      (S.filter fun g => (fun y => (v x y).eval g) = cand g x).card ≤ 28 := by
    intro x hx
    obtain ⟨y,hy⟩ : ∃ y, v x y ≠ interp I cand x y := by
      simpa only [Bad, mem_filter, not_forall] using (mem_filter.mp hx).2
    let diff := v x y - interp I cand x y
    have hdiff : diff ≠ 0 := sub_ne_zero.mpr hy
    have hinterp : (interp I cand x y).degree < 29 := by
      simpa [interp, Lagrange.interpolate_apply, hI] using
        Lagrange.degree_interpolate_lt
          (r := fun g => cand g x y) (s := I) (v := id)
          (fun _ _ _ _ h => h)
    have hdiffdeg : diff.natDegree ≤ 28 := by
      have hd : diff.degree < 29 :=
        (degree_sub_le _ _).trans_lt (max_lt (degree x y) hinterp)
      have hn : diff.natDegree < 29 := (natDegree_lt_iff_degree_lt hdiff).mpr hd
      omega
    have hroot := root_count S diff hdiff 28 hdiffdeg
    apply le_trans (card_le_card ?_) hroot
    intro g hg
    have hmatch := (mem_filter.mp hg).2
    apply mem_filter.mpr
    refine ⟨(mem_filter.mp hg).1, ?_⟩
    dsimp [diff]
    rw [eval_sub, sub_eq_zero, ← congrFun (congrFun (candEq g (mem_filter.mp hg).1) x) y]
    exact congrFun hmatch y
  have badMiss : ∀ x ∈ Bad,
      36 ≤ (S.filter fun g => (fun y => (v x y).eval g) ≠ cand g x).card := by
    intro x hx
    have split :
        (S.filter fun g => (fun y => (v x y).eval g) = cand g x).card +
        (S.filter fun g => (fun y => (v x y).eval g) ≠ cand g x).card = S.card := by
      simpa using card_filter_add_card_filter_not
        (s := S) (fun g => (fun y => (v x y).eval g) = cand g x)
    have cap := badRoots x hx
    rw [hS] at split
    omega
  have incidence := Finset.card_nsmul_le_card_nsmul (R := Nat)
    (s := Bad) (t := S)
    (fun x g => (fun y => (v x y).eval g) ≠ cand g x)
    badMiss
    (by
      intro g hg
      apply le_trans (card_le_card ?_) (near g hg)
      intro x hx
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,
        (mem_filter.mp hx).2⟩)
  simp only [nsmul_eq_mul] at incidence
  change Bad.card * 36 ≤ S.card * 9301 at incidence
  have badCap : Bad.card ≤ 16535 := by
    rw [hS] at incidence
    omega
  have split := card_filter_add_card_filter_not
    (s := D) (fun x => ∀ y, v x y = interp I cand x y)
  have badEq : (D.filter fun x => ¬ ∀ y, v x y = interp I cand x y) = Bad := rfl
  rw [badEq, hD] at split
  omega

#print axioms own_support_64_29
end AspisV8.NearGammaOwnSupport
