-- PCWG_ generic lemmas for NCX_Reference.zero / required_binding_is_zero against the frozen array-equality emission.
import Aeneas
import PRVEq_P3W_LoopMap
import NCX_Reference.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace PRVEq_P3Y

theorem allM_ok {α : Type} (p : α → Bool) (l : List α) :
    List.allM (fun x => (ok (p x) : Result Bool)) l = ok (l.all p) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.allM, ih]

theorem zip_all_eq {α : Type} [DecidableEq α] (l1 l2 : List α) (h : l1.length = l2.length) :
    ((l1.zip l2).all (fun p => decide (p.1 = p.2))) = decide (l1 = l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a t ih =>
    cases l2 with
    | nil => simp at h
    | cons b u =>
      simp at h
      simp [List.zip_cons_cons, ih u h]

/-- array equality emission (core.array.equality.PartialEqArray.eq at u8) is the pure list equality -/
theorem arr_eq_u8 {N : Std.Usize} (a b : Std.Array Std.U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a b = ok (decide (a.val = b.val)) := by
  unfold core.array.equality.PartialEqArray.eq
  have hl : a.length = b.length := by simp [Std.Array.length]
end PRVEq_P3Y
