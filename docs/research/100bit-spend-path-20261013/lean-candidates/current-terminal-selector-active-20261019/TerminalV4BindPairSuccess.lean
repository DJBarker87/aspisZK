import TerminalV4ActiveLiteralClosureV2
open Aeneas Aeneas.Std Result ControlFlow Error WP
set_option autoImplicit false
namespace AspisR1.TerminalV4BindPairSuccess

theorem bind_pair_ok_inv {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (x, y) ← m; k x y) = .ok v) :
    ∃ x y, m = .ok (x, y) ∧ k x y = .ok v := by
  cases m with
  | ok pair =>
      rcases pair with ⟨x, y⟩
      simp only [bind_tc_ok] at h
      exact ⟨x, y, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

#print axioms bind_pair_ok_inv
end AspisR1.TerminalV4BindPairSuccess
