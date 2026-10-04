import AspisV8R19.GuardedFirstRead

/-! A quantitative comparison that charges cache hits instead of assuming
whole-program freshness. It includes arbitrary trace/result tests in [0,1].
The actual source-specific first-hit probability still must be bounded. -/
set_option autoImplicit false
namespace AspisV8R19.R413GuardedOracleDistance
open OracleResampling MemoizedProgramLaw AdaptiveFirstReadLaw GuardedFirstRead
open AspisV8PairedCommitment
noncomputable section
variable {X I A O : Type}

theorem mean_mono [Fintype X] (f g : X → ℚ) (h : ∀ x, f x ≤ g x) :
    mean f ≤ mean g := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

theorem mean_interval [Fintype X] [Nonempty X] (f : X → ℚ)
    (h : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : 0 ≤ mean f ∧ mean f ≤ 1 := by
  constructor
  · have hh := mean_mono (fun _ : X => 0) f (fun x => (h x).1)
    simpa only [mean_const] using hh
  · have hh := mean_mono f (fun _ : X => 1) (fun x => (h x).2)
    simpa only [mean_const] using hh

theorem mean_sub [Fintype X] (f g : X → ℚ) :
    mean f - mean g = mean (fun x => f x-g x) := by
  simp only [mean,Finset.sum_sub_distrib,sub_div]

theorem abs_mean_le [Fintype X] (f : X → ℚ) :
    |mean f| ≤ mean (fun x => |f x|) := by
  simp only [mean,abs_div,abs_of_nonneg (show 0 ≤ (Fintype.card X : ℚ) by positivity)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)

theorem independent_interval [Fintype A] [Nonempty A]
    (p : Program I A O) (observe : View I A O → ℚ)
    (bounded : ∀ v, 0 ≤ observe v ∧ observe v ≤ 1) :
    0 ≤ independentMean p observe ∧ independentMean p observe ≤ 1 := by
  induction p generalizing observe with
  | done o => exact bounded ([],o)
  | ask i next ih =>
      apply mean_interval
      intro a
      exact ih a _ (fun v => bounded ((i,a)::v.1,v.2))

theorem lazy_interval [Fintype A] [Nonempty A] [DecidableEq I]
    (p : Program I A O) (t : Table I A) (observe : View I A O → ℚ)
    (bounded : ∀ v, 0 ≤ observe v ∧ observe v ≤ 1) :
    0 ≤ lazyMean p t observe ∧ lazyMean p t observe ≤ 1 := by
  induction p generalizing t observe with
  | done o => exact bounded ([],o)
  | ask i next ih =>
      cases ht : t i with
      | none =>
          simp only [lazyMean,ht]
          apply mean_interval
          intro a
          exact ih a _ _ (fun v => bounded ((i,a)::v.1,v.2))
      | some a =>
          simp only [lazyMean,ht]
          exact ih a _ _ (fun v => bounded ((i,a)::v.1,v.2))

theorem guarded_distance [Fintype A] [Nonempty A] [DecidableEq I]
    (p : Program I A O) (t : Table I A) (observe : View I A O → ℚ)
    (bounded : ∀ v, 0 ≤ observe v ∧ observe v ≤ 1) :
    |lazyMean p t observe - independentMean p observe| ≤
      independentMean (guardFresh p t) (fun v => if v.2 = none then 1 else 0) := by
  classical
  induction p generalizing t observe with
  | done o => simp [lazyMean,independentMean,guardFresh]
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          have hl := lazy_interval (.ask i next) t observe bounded
          have hr := independent_interval (.ask i next) observe bounded
          simp only [independentMean] at hr
          rcases hl with ⟨hl0,hl1⟩
          rcases hr with ⟨hr0,hr1⟩
          simp only [guardFresh,ht,independentMean,↓reduceIte]
          apply abs_le.mpr
          constructor <;> linarith
      | none =>
          simp only [lazyMean,ht,independentMean,guardFresh]
          rw [mean_sub]
          apply (abs_mean_le _).trans
          apply mean_mono
          intro a
          exact ih a (put t i a) _ (fun v => bounded ((i,a)::v.1,v.2))

#print axioms mean_mono
#print axioms mean_interval
#print axioms mean_sub
#print axioms abs_mean_le
#print axioms independent_interval
#print axioms lazy_interval
#print axioms guarded_distance
end
end AspisV8R19.R413GuardedOracleDistance
