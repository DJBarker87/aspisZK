import RPu_FJa_SplitModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_FoldShape
open FIv_NativeValue (K)
open FJa_SplitModel (step fold)
/-- Finished descending writes do not affect the unvisited upper suffix. -/
theorem outside (c : K) (f : Nat → K) (n j : Nat) (hj : 2*n≤j) : fold c n f j=f j := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [fold,ih _ (by omega),FJa_SplitModel.outside c f n j (by omega)]
/-- A completed split is the literal two-child tensor extension at every
visited parent, without evaluation of any concrete 64-cell recurrence. -/
theorem children (c : K) (f : Nat → K) (n i : Nat) (hi : i < n) :
    fold c n f (2*i)=f i-c*f i ∧ fold c n f (2*i+1)=c*f i := by
  induction n generalizing f with
  | zero => omega
  | succ n ih =>
    by_cases he : i=n
    · subst i
      simp only [fold]
      rw [outside c (step c f n) n (2*n) (by omega),
        outside c (step c f n) n (2*n+1) (by omega)]
      exact ⟨FJa_SplitModel.left c f n,FJa_SplitModel.right c f n⟩
    · have hlt : i < n := by omega
      have h := ih (step c f n) hlt
      simpa only [fold,FJa_SplitModel.lower c f n i hlt] using h
#print axioms outside
#print axioms children
end AspisR1.FJa_FoldShape
end
