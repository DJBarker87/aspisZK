import CantorZassenhausSplit
import FiniteFieldModularPower

noncomputable section
namespace AspisR1.CantorZassenhausFastTrial
open Polynomial AspisR1.CantorZassenhausSplit AspisR1.CantorZassenhausPair
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem modularPower_eval_at_root (f h : K[X]) (hf : f.Monic)
    (hdeg : (0 : WithBot Nat)<degree f) (x : K) (hx : IsRoot f x) (e : Nat) :
    (polynomialModPower h f e).eval x = (h.eval x)^e := by
  rcases polynomialModPower_congruent h f hf hdeg e with ⟨g,hg⟩
  have he := congrArg (fun p : K[X] => p.eval x) hg
  change f.eval x = 0 at hx
  simp only [eval_sub,eval_pow,eval_mul,hx,zero_mul] at he
  exact sub_eq_zero.mp he

/-- Explicit q is supplied, never computed by enumerating K. -/
def FastTrialSuccess (f h : K[X]) (q : Nat) : Prop :=
  ProperFactor (monicGCD f h) f ∨
  ProperFactor (monicGCD f (polynomialModPower h f (q/2)-1)) f

/-- Divisibility is automatic for a gcd, so the test uses only equality checks. -/
instance properGCDDecidable (f h : K[X]) : Decidable (ProperFactor (monicGCD f h) f) :=
  decidable_of_iff
    (monicGCD f h ≠ 1 ∧ monicGCD f h ≠ f)
    (by simp only [ProperFactor,monicGCD_dvd_left,true_and])

instance fastTrialSuccessDecidable (f h : K[X]) (q : Nat) : Decidable (FastTrialSuccess f h q) := by
  unfold FastTrialSuccess
  infer_instance

theorem different_categories_fast_split (f h : K[X]) (a b : K) (q : Nat)
    (hq : q=Fintype.card K) (hf : f.Monic) (hdeg : (0 : WithBot Nat)<degree f)
    (hodd : ringChar K ≠ 2) (hfa : IsRoot f a) (hfb : IsRoot f b)
    (hchi : quadraticChar K (h.eval a) ≠ quadraticChar K (h.eval b)) :
    FastTrialSuccess f h q := by
  have hpa := quadraticChar_eq_pow_of_char_ne_two' hodd (h.eval a)
  have hpb := quadraticChar_eq_pow_of_char_ne_two' hodd (h.eval b)
  have hea := modularPower_eval_at_root f h hf hdeg a hfa (q/2)
  have heb := modularPower_eval_at_root f h hf hdeg b hfb (q/2)
  rw [hq] at hea heb
  rw [←hea] at hpa
  rw [←heb] at hpb
  by_cases ha : h.eval a=0
  · have hb : h.eval b ≠ 0 := by
      intro hb
      exact hchi (by rw [ha,hb])
    exact Or.inl (proper_gcd_of_separated_roots f h a b hfa hfb ha hb)
  · by_cases hb : h.eval b=0
    · exact Or.inl (proper_gcd_of_separated_roots f h b a hfb hfa hb ha)
    · have hnot : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hodd
      rw [←hq] at hpa hpb
      rcases quadraticChar_dichotomy (F := K) ha with hca|hca <;>
      rcases quadraticChar_dichotomy (F := K) hb with hcb|hcb
      · exact (hchi (hca.trans hcb.symm)).elim
      · apply Or.inr
        apply proper_gcd_of_separated_roots f (polynomialModPower h f (q/2)-1) a b hfa hfb
        · rw [IsRoot,eval_sub,eval_one,←hpa,hca]; simp
        · rw [IsRoot,eval_sub,eval_one,←hpb,hcb]
          simpa only [Int.cast_neg,Int.cast_one,sub_eq_zero] using hnot
      · apply Or.inr
        apply proper_gcd_of_separated_roots f (polynomialModPower h f (q/2)-1) b a hfb hfa
        · rw [IsRoot,eval_sub,eval_one,←hpb,hcb]; simp
        · rw [IsRoot,eval_sub,eval_one,←hpa,hca]
          simpa only [Int.cast_neg,Int.cast_one,sub_eq_zero] using hnot
      · exact (hchi (hca.trans hcb.symm)).elim

def randomLinear (c : K × K) : K[X] := C c.1 + C c.2 * X

theorem randomLinear_eval (c : K × K) (x : K) :
    (randomLinear c).eval x = c.1+c.2*x := by simp [randomLinear]

def fastFailure (f : K[X]) (q : Nat) (c : K × K) : ℚ :=
  if FastTrialSuccess f (randomLinear c) q then 0 else 1

theorem fastFailure_le_sameCategory (f : K[X]) (a b : K) (q : Nat)
    (hq : q=Fintype.card K) (hf : f.Monic) (hdeg : (0 : WithBot Nat)<degree f)
    (hodd : ringChar K ≠ 2) (hfa : IsRoot f a) (hfb : IsRoot f b) (c : K × K) :
    fastFailure f q c ≤ sameCategory (c.1+c.2*a) (c.1+c.2*b) := by
  by_cases hc : quadraticChar K (c.1+c.2*a) = quadraticChar K (c.1+c.2*b)
  · unfold fastFailure
    simp only [sameCategory,if_pos hc]
    split <;> norm_num
  · have hd : quadraticChar K ((randomLinear c).eval a) ≠
        quadraticChar K ((randomLinear c).eval b) := by simpa only [randomLinear_eval] using hc
    have hs := different_categories_fast_split f (randomLinear c) a b q hq hf hdeg hodd hfa hfb hd
    simp only [fastFailure,if_pos hs,sameCategory,if_neg hc,le_refl]

theorem linear_fast_trial_failure_le_half (f : K[X]) (a b : K) (q : Nat)
    (hq : q=Fintype.card K) (hf : f.Monic) (hdeg : (0 : WithBot Nat)<degree f)
    (hab : a≠b) (hodd : ringChar K ≠ 2) (hfa : IsRoot f a) (hfb : IsRoot f b) :
    (∑ c : K × K, fastFailure f q c) / ((q : ℚ)^2) ≤ 1/2 := by
  have hsum : (∑ c : K × K, fastFailure f q c) ≤
      ∑ c : K × K, sameCategory (c.1+c.2*a) (c.1+c.2*b) :=
    Finset.sum_le_sum (fun c _ => fastFailure_le_sameCategory f a b q hq hf hdeg hodd hfa hfb c)
  calc
    _ ≤ (∑ c : K × K, sameCategory (c.1+c.2*a) (c.1+c.2*b)) / ((q : ℚ)^2) :=
      div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ ≤ 1/2 := by
      rw [hq]
      simpa only [add_zero] using affine_pair_failure_le_half a b 0 0 hab hodd

#print axioms modularPower_eval_at_root
#print axioms different_categories_fast_split
#print axioms linear_fast_trial_failure_le_half
end AspisR1.CantorZassenhausFastTrial
