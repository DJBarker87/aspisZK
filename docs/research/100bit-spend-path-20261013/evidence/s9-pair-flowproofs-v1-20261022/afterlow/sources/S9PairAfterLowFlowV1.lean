import S9PairCallerBodyPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9PairAfterLowFlowV1
open AspisR1S9PairCallerBodyPrefixV1
private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem afterlow_success_preserves_iter
    (ap1 : W) (side : U) (iterNext : R) (weights : W)
    (q41 q8 q12 q16 : Q) (low : AspisR1S9PairCallerStepV1.field.WideExact)
    (flow : ControlFlow (R × W) W)
    (h : pairAfterLow ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow) :
    ∃ output, flow = .cont (iterNext, output) := by
  unfold pairAfterLow at h
  repeat' rcases bind_success_inv _ _ _ h with ⟨_, _, h⟩
  by_cases hs : side = 0#usize
  · simp only [if_pos hs] at h
    repeat' rcases bind_success_inv _ _ _ h with ⟨_, _, h⟩
    exact ⟨_, (Result.ok.inj h).symm⟩
  · simp only [if_neg hs] at h
    repeat' rcases bind_success_inv _ _ _ h with ⟨_, _, h⟩
    exact ⟨_, (Result.ok.inj h).symm⟩

#print axioms afterlow_success_preserves_iter
end AspisR1S9PairAfterLowFlowV1
