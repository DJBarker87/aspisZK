import BatchedWeightsPushQueryGeneratedBridgeV9
import AspisR1BatchedWeightsExtraction.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace BatchedWeightsPushQueryGeneratedBridgeV10
 theorem loop_success_cases {α β : Type} (body : α → Result (ControlFlow α β))
    (x : α) (out : β) (h : Aeneas.Std.loop body x = .ok out) :
    body x = .ok (.done out) ∨ ∃ x', body x = .ok (.cont x') ∧
      Aeneas.Std.loop body x' = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hb : body x with
  | fail e => simp [hb] at h
  | div => simp [hb] at h
  | ok cf =>
    cases cf with
    | done y =>
      simp [hb] at h
      subst y
      exact Or.inl rfl
    | cont y =>
      simp [hb] at h
      exact Or.inr ⟨y, rfl, h⟩
#print axioms loop_success_cases
end BatchedWeightsPushQueryGeneratedBridgeV10
