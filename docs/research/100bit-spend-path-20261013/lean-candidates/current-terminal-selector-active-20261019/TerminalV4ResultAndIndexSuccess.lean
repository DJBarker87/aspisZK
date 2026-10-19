import TerminalV4ActiveLiteralClosureV2
open Aeneas Aeneas.Std Result ControlFlow Error WP
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace AspisR1.TerminalV4ResultAndIndexSuccess

theorem bind_ok_inv {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem array_index_ok_lt {α : Type} (a : Array α 16#usize) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < a.val.length := by
  by_cases hi : i.val < a.val.length
  · exact hi
  · have hge : a.val.length ≤ i.val := Nat.le_of_not_gt hi
    unfold Array.index_usize at h
    change (match a.val[i.val]? with | none => Result.fail Error.arrayOutOfBounds | some y => Result.ok y) = .ok x at h
    have hnone : a.val[i.val]? = none := List.getElem?_eq_none_iff.mpr hge
    rw [hnone] at h
    cases h

#print axioms bind_ok_inv
#print axioms array_index_ok_lt
end AspisR1.TerminalV4ResultAndIndexSuccess
