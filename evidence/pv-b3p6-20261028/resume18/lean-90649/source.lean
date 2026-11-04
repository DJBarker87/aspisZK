import PV_B3P_InitializerEvents578227
namespace PV_B3P_SliceMetadata581227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- An ordered wrapped endpoint implies addition did not wrap. Both scalar
bounds are intrinsic to the source Usize inputs, not new caller hypotheses. -/
theorem ordered_wrapped_width (start width : Usize)
    (ordered : start.val ≤ (Usize.wrapping_add start width).val) :
    (Usize.wrapping_add start width).val - start.val = width.val := by
  have sb : start.val < UScalar.size .Usize := by simpa only [UScalar.size] using start.hBounds
  have wb : width.val < UScalar.size .Usize := by simpa only [UScalar.size] using width.hBounds
  rw [Usize.wrapping_add_val_eq] at ordered ⊢
  by_cases nowrap : start.val+width.val < UScalar.size .Usize
  · rw [Nat.mod_eq_of_lt nowrap]
    omega
  · have subtract : (start.val+width.val) % UScalar.size .Usize =
        start.val+width.val-UScalar.size .Usize := by
      rw [Nat.mod_eq_sub_mod (by omega : UScalar.size .Usize ≤ start.val+width.val)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [subtract] at ordered
    omega

/-- Metadata observation of a successful safe range-index prefix. Invalid
bounds produce no downstream pack-input observation. This is not a model of
panic formatting, observable failure effects, or the slice element pointer. -/
def sourceEvent (start width : Usize) (capacity slack : Nat)
    (effects : List (Result Unit)) : Result (Option IndexState) :=
  let finish := Usize.wrapping_add start width
  if start.val ≤ finish.val ∧ finish.val ≤ capacity then
    through effects (some ⟨finish.val-start.val,width.val+slack⟩)
  else .ok none

theorem event_guard (start width : Usize) (capacity slack : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent start width capacity slack effects = .ok (some observed)) :
    observed.index ≤ observed.length := by
  by_cases valid : start.val ≤ (Usize.wrapping_add start width).val ∧
      (Usize.wrapping_add start width).val ≤ capacity
  · simp only [sourceEvent,if_pos valid] at ran
    have frame := through_value _ _ _ ran
    cases frame
    change (Usize.wrapping_add start width).val-start.val ≤ width.val+slack
    rw [ordered_wrapped_width start width valid.1]
    omega
  · simp only [sourceEvent,if_neg valid] at ran
    cases ran

theorem event_certificate {α : Type} (start width : Usize) (capacity slack : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent start width capacity slack effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (decide (observed.index ≤ observed.length) = true) ∧
      branch (decide (observed.index ≤ observed.length) = true) normal first =
        branch (decide (observed.index ≤ observed.length) = true) normal second :=
  (assertion _ true normal first second).2
    (decide_eq_true (event_guard start width capacity slack effects observed ran))
#print axioms ordered_wrapped_width
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_SliceMetadata581227
