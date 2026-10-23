import S9ActualPairHelperBodyPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ActualPairHelperActiveFlowV1
open AspisR1S9ActualPairHelperBodyPrefixV1
private def ContinuesAt (iter : R) (m : Result (ControlFlow (R × W) W)) : Prop :=
  ∀ out, m = .ok out → ∃ weights, out = .cont (iter,weights)
private theorem bind_continuesAt {A : Type} (iter : R) (m : Result A)
    (k : A → Result (ControlFlow (R × W) W))
    (hk : ∀ x, ContinuesAt iter (k x)) : ContinuesAt iter (do let x ← m; k x) := by
  intro out h
  cases hm : m with
  | fail e => simp only [hm,bind_tc_fail] at h; cases h
  | div => simp only [hm,bind_tc_div] at h; cases h
  | ok x => simp only [hm,bind_tc_ok] at h; exact hk x out h

/-- Structural accepted-flow fact, uniform in all source arithmetic outcomes.
This reuses the named exact active source body; no arithmetic is assumed. -/
theorem active_success_preserves_iter
    (ap0 ap1 : W) (extra : Array Q 2#usize) (side : U) (iterNext : R)
    (weights : W) (flow : ControlFlow (R × W) W)
    (h : pairActiveBody ap0 ap1 extra side iterNext weights = .ok flow) :
    ∃ output, flow = .cont (iterNext,output) := by
  have hc : ContinuesAt iterNext (pairActiveBody ap0 ap1 extra side iterNext weights) := by
    unfold pairActiveBody pairAfterLow
    repeat (apply bind_continuesAt; intro)
    split
    all_goals repeat (apply bind_continuesAt; intro)
    all_goals
      intro result hr
      exact ⟨_,(Result.ok.inj hr).symm⟩
  exact hc flow h
#print axioms active_success_preserves_iter
end AspisR1S9ActualPairHelperActiveFlowV1
