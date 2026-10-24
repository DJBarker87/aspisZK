import S9ActualPairHelperScalarDispatchV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualPairScalarCallbackV1 AspisR1S9ActualPairScalarFoldV1
namespace AspisR1S9ActualPairScalarFoldJoinV1
local instance helperOps : AspisR1S9HelperP6.FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

theorem actual_fold_success_to_helper (range : R) (initial out : W) (c : SC)
    (hp : GoodArray c.1) (hinit : Canonical initial)
    (h : core.iter.traits.iterator.Iterator.fold.default
      (Aeneas.Std.core.iter.traits.iterator.IteratorRange Aeneas.Std.core.iter.range.StepUsize)
      sourceCallback range initial c = .ok out) :
    Canonical out ∧
      @AspisR1S9HelperP6.FieldOps.iterFold AspisR1S9ConcreteFieldOpsV1.concreteFieldOps _ _ _ _
        (Aeneas.Std.core.iter.traits.iterator.IteratorRange Aeneas.Std.core.iter.range.StepUsize)
        helperCallback range (toHelperW initial) (mapClosure c) = .ok (toHelperW out) := by
  rw [AspisR1S9ActualPairFoldRunV1.actual_fold_eq_range_run] at h
  obtain ⟨pair,hrange,hvalue⟩ := bind_success _ _ _ h
  rcases pair with ⟨value,capOut⟩
  have heq : value = out := Result.ok.inj hvalue
  subst value
  obtain ⟨hcap,hcan,htarget⟩ := scalar_range_run_success
    (range.end.val-range.start.val) range c capOut initial out hp hinit hrange
  refine ⟨hcan,?_⟩
  rw [AspisR1S9ActualPairHelperScalarDispatchV1.helper_fold_eq_range_run]
  change (do
    let (v,_) ← AspisR1S3S9RangeFoldP6.rangeFoldRun (range.end.val-range.start.val) range
      (AspisR1S9TransparentFoldRangeLawV1.foldStep helperCallback) (mapState (initial,c))
    ok v) = .ok (toHelperW out)
  rw [htarget]
  rfl
#print axioms actual_fold_success_to_helper
end AspisR1S9ActualPairScalarFoldJoinV1
