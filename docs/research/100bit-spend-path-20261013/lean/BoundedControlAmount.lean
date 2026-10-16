import BoundedControlSource
import BoundedControlArithmetic
import TerminalAmountGuardClosure
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisBoundedControl.Amount
open Aeneas Aeneas.Std Result
open AspisBoundedControl Arithmetic

/-- Actual explicit-match candidate agrees with the old retained guard closure
on the Some branch; no model for the unsupported Option method is assumed. -/
theorem some_agrees_with_old_closure (a : Std.U32) :
    invalid_amount (some a) =
      AspisR1TerminalAmountGuardSlice.amount_guard_call_once () a := by
  unfold invalid_amount AspisR1TerminalAmountGuardSlice.amount_guard_call_once
  dsimp only
  by_cases hz : a = 0#u32
  · simp only [hz, if_true]
  · rw [if_neg hz, if_neg hz]
    have hlimit : (1#u32 <<< 30#i32) = .ok 1073741824#u32 := by rfl
    rw [hlimit]
    rfl

theorem false_implies_range (amount : Option Std.U32)
    (h : invalid_amount amount = .ok false) :
    amount = none ∨ ∃ a : Std.U32,
      amount = some a ∧ 0 < a.val ∧ a.val < 2 ^ 30 := by
  cases amount with
  | none => exact Or.inl rfl
  | some a =>
    rw [some_agrees_with_old_closure] at h
    obtain ⟨hpos, hlt⟩ :=
      AspisR1TerminalAmountGuardSlice.false_implies_amount_range a h
    exact Or.inr ⟨a, rfl, hpos, hlt⟩

#print axioms some_agrees_with_old_closure
#print axioms false_implies_range
end AspisBoundedControl.Amount
