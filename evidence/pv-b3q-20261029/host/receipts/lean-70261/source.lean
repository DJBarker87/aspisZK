import PV_B3Q_SliceEqual
namespace PV_B3Q_SliceSuffix
open Aeneas Aeneas.Std PV_B3Q_SliceEqual
set_option autoImplicit false
/-- The source index denotes the head of the unconsumed slice suffix. -/
theorem read_suffix {α : Type} (xs : List α) (index : Nat) :
    read xs index = match xs.drop index with | [] => .fail .arrayOutOfBounds | x::_ => .ok x := by
 induction xs generalizing index with
 | nil => cases index <;> rfl
 | cons x xs ih =>
   cases index with
   | zero => rfl
   | succ index => exact ih index

theorem suffix_advance {α : Type} (xs : List α) (index : Nat) :
    (xs.drop index).drop 1 = xs.drop (index+1) := by
 induction xs generalizing index with
 | nil => cases index <;> rfl
 | cons x xs ih =>
   cases index with
   | zero => rfl
   | succ index => exact ih index

def tail_loop {α β : Type} (ne : α → β → Result Bool) :
    Nat → List α → List β → Result Bool
 | 0,_,_ => .ok true
 | remaining+1,left,right => do
   let x ← match left with | [] => .fail .arrayOutOfBounds | x::_ => .ok x
   let y ← match right with | [] => .fail .arrayOutOfBounds | y::_ => .ok y
   let different ← ne x y
   if different then .ok false else tail_loop ne remaining (left.drop 1) (right.drop 1)
/-- Changes the loop state representation only; failure/divergence and early
false return remain in the same order, including empty invalid inputs. -/
theorem loop_suffix_binding {α β : Type} (ne : α → β → Result Bool)
    (left : List α) (right : List β) (remaining index : Nat) :
    source_loop ne left right remaining index =
      tail_loop ne remaining (left.drop index) (right.drop index) := by
 induction remaining generalizing index with
 | zero => rfl
 | succ remaining ih =>
   simp only [source_loop,compare_at,read_suffix,tail_loop]
   cases hl : left.drop index with
   | nil => rfl
   | cons x xs =>
     cases hr : right.drop index with
     | nil => rfl
     | cons y ys =>
       simp only [bind_tc_ok]
       cases ne x y with
       | fail e => rfl
       | div => rfl
       | ok different =>
         cases different
         · simp only [bind_tc_ok,Bool.false_eq_true,↓reduceIte]
           rw [ih,←suffix_advance left index,←suffix_advance right index,hl,hr]
         · rfl
#print axioms read_suffix
#print axioms suffix_advance
#print axioms loop_suffix_binding
end PV_B3Q_SliceSuffix
