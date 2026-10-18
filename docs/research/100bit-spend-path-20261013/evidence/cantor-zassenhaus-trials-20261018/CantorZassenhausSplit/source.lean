import CantorZassenhausPair
import Mathlib.Algebra.Polynomial.FieldDivision

noncomputable section
namespace AspisR1.CantorZassenhausSplit
open Polynomial
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Euclidean gcds need not be monic. Normalize before every factor test. -/
def monicGCD (f h : K[X]) : K[X] := normalize (EuclideanDomain.gcd f h)

theorem monicGCD_dvd_left (f h : K[X]) : monicGCD f h ∣ f := by
  unfold monicGCD
  rw [normalize_dvd_iff]
  exact EuclideanDomain.gcd_dvd_left _ _

theorem monicGCD_root_iff (f h : K[X]) (x : K) :
    IsRoot (monicGCD f h) x ↔ IsRoot f x ∧ IsRoot h x := by
  unfold monicGCD
  rw [←Polynomial.dvd_iff_isRoot,dvd_normalize_iff,Polynomial.dvd_iff_isRoot,
    Polynomial.isRoot_gcd_iff_isRoot_left_right]

theorem monicGCD_monic (f h : K[X]) (hf : f ≠ 0) : (monicGCD f h).Monic := by
  apply Polynomial.monic_normalize
  intro hz
  have hd := EuclideanDomain.gcd_dvd_left f h
  rw [hz] at hd
  exact hf (zero_dvd_iff.mp hd)

def ProperFactor (d f : K[X]) : Prop := d ∣ f ∧ d ≠ 1 ∧ d ≠ f

theorem proper_gcd_of_separated_roots (f h : K[X]) (a b : K)
    (hfa : IsRoot f a) (hfb : IsRoot f b)
    (hha : IsRoot h a) (hhb : ¬ IsRoot h b) :
    ProperFactor (monicGCD f h) f := by
  refine ⟨monicGCD_dvd_left _ _, ?_, ?_⟩
  · intro heq
    have hr := (monicGCD_root_iff f h a).mpr ⟨hfa,hha⟩
    rw [heq] at hr
    simpa [IsRoot] using hr
  · intro heq
    have hr : IsRoot (monicGCD f h) b := by rw [heq]; exact hfb
    exact hhb ((monicGCD_root_iff f h b).mp hr).2

theorem proper_monic_factor_degrees (d f : K[X]) (hdm : d.Monic) (hfm : f.Monic)
    (hd : ProperFactor d f) : 0 < d.natDegree ∧ d.natDegree < f.natDegree := by
  constructor
  · apply Nat.pos_of_ne_zero
    intro hn
    exact hd.2.1 (hdm.natDegree_eq_zero.mp hn)
  · by_contra hn
    have he : f=d := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hdm hfm hd.1 (by omega)
    exact hd.2.2 he.symm

/-- Both gcd checks are necessary for the clean one-half trial bound. -/
def TwoGCDSplit (f h : K[X]) : Prop :=
  ProperFactor (monicGCD f h) f ∨
  ProperFactor (monicGCD f (h^(Fintype.card K / 2)-1)) f

theorem different_categories_split (f h : K[X]) (a b : K)
    (hodd : ringChar K ≠ 2) (hfa : IsRoot f a) (hfb : IsRoot f b)
    (hchi : quadraticChar K (h.eval a) ≠ quadraticChar K (h.eval b)) :
    TwoGCDSplit f h := by
  by_cases ha : h.eval a=0
  · have hb : h.eval b ≠ 0 := by
      intro hb
      exact hchi (by rw [ha,hb])
    exact Or.inl (proper_gcd_of_separated_roots f h a b hfa hfb ha hb)
  · by_cases hb : h.eval b=0
    · exact Or.inl (proper_gcd_of_separated_roots f h b a hfb hfa hb ha)
    · have hpa := quadraticChar_eq_pow_of_char_ne_two' hodd (h.eval a)
      have hpb := quadraticChar_eq_pow_of_char_ne_two' hodd (h.eval b)
      have hnot : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hodd
      rcases quadraticChar_dichotomy (F := K) ha with hca|hca <;>
      rcases quadraticChar_dichotomy (F := K) hb with hcb|hcb
      · exact (hchi (hca.trans hcb.symm)).elim
      · apply Or.inr
        apply proper_gcd_of_separated_roots f (h^(Fintype.card K / 2)-1) a b hfa hfb
        · rw [IsRoot,eval_sub,eval_pow,eval_one,←hpa,hca]
          simp
        · rw [IsRoot,eval_sub,eval_pow,eval_one,←hpb,hcb]
          simpa only [Int.cast_neg,Int.cast_one,sub_eq_zero] using hnot
      · apply Or.inr
        apply proper_gcd_of_separated_roots f (h^(Fintype.card K / 2)-1) b a hfb hfa
        · rw [IsRoot,eval_sub,eval_pow,eval_one,←hpb,hcb]
          simp
        · rw [IsRoot,eval_sub,eval_pow,eval_one,←hpa,hca]
          simpa only [Int.cast_neg,Int.cast_one,sub_eq_zero] using hnot
      · exact (hchi (hca.trans hcb.symm)).elim

#print axioms monicGCD_root_iff
#print axioms monicGCD_monic
#print axioms proper_monic_factor_degrees
#print axioms proper_gcd_of_separated_roots
#print axioms different_categories_split
end AspisR1.CantorZassenhausSplit
