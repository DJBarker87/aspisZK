import PV_B3P_RustResult
namespace PV_B3P_ResultSuccess226
open Aeneas Aeneas.Std PV_B3P_RustResult
set_option autoImplicit false

theorem bind_success {α β E : Type} (x : Result (core.result.Result α E))
    (k : α → Result (core.result.Result β E)) (b : β) :
    bindR x k = .ok (.Ok b) ↔
      ∃ a, x = .ok (.Ok a) ∧ k a = .ok (.Ok b) := by
  cases x with
  | ok r => cases r <;> simp [bindR]
  | fail e => simp [bindR]
  | div => simp [bindR]

theorem collect_success {α E : Type} (xs : List (Result (core.result.Result α E)))
    (h : ∀ x ∈ xs, ∃ a, x = .ok (.Ok a)) :
    ∃ ys, collect xs = .ok (.Ok ys) ∧ ys.length = xs.length := by
  induction xs with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨a,ha⟩ := h x (by simp)
    have ht : ∀ y ∈ xs, ∃ b, y = .ok (.Ok b) := by
      intro y hy
      exact h y (by simp only [List.mem_cons]; exact Or.inr hy)
    obtain ⟨ys,hys,hlen⟩ := ih ht
    refine ⟨a::ys,?_,by simp [hlen]⟩
    simp only [collect,ha,bindR,hys]

theorem collect_length {α E : Type} (xs : List (Result (core.result.Result α E)))
    (ys : List α) (h : collect xs = .ok (.Ok ys)) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simp only [collect] at h; cases h; rfl
  | cons x xs ih =>
    rw [collect,bind_success] at h
    obtain ⟨a,_,h⟩ := h
    rw [bind_success] at h
    obtain ⟨rest,hrest,hout⟩ := h
    have heq : a::rest = ys := by cases hout; rfl
    rw [← heq]
    simp only [List.length_cons,ih rest hrest]

#print axioms bind_success
#print axioms collect_success
#print axioms collect_length
end PV_B3P_ResultSuccess226
