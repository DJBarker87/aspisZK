import PV_B3P_ClosureLinks14227
namespace PV_B3Q_SliceEqual
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- Source checked indexing, including the otherwise unreachable panic branch. -/
def read {α : Type} (xs : List α) (index : Nat) : Result α :=
 match xs[index]? with
 | none => .fail .arrayOutOfBounds
 | some x => .ok x
/-- One source comparison, preserving both indexed-read errors and the comparator's
complete Result; shared reads leave both backing slices unchanged. -/
def compare_at {α β : Type} (ne : α → β → Result Bool)
    (left : List α) (right : List β) (index : Nat) : Result Bool := do
 let x ← read left index
 let y ← read right index
 ne x y
/-- remaining = len-index is a proof measure, never a new Rust input. -/
def source_loop {α β : Type} (ne : α → β → Result Bool)
    (left : List α) (right : List β) : Nat → Nat → Result Bool
 | 0, _ => .ok true
 | remaining+1, index => do
    let different ← compare_at ne left right index
    if different then .ok false else source_loop ne left right remaining (index+1)
def ordered {α β : Type} (ne : α → β → Result Bool)
    (left : List α) (right : List β) : List Nat → Result Bool
 | [] => .ok true
 | index::rest => do
    let different ← compare_at ne left right index
    if different then .ok false else ordered ne left right rest
def source {α β : Type} (ne : α → β → Result Bool)
    (left : List α) (right : List β) : Result Bool :=
 if left.length != right.length then .ok false else source_loop ne left right left.length 0
def model {α β : Type} (ne : α → β → Result Bool)
    (left : List α) (right : List β) : Result Bool :=
 if left.length != right.length then .ok false else ordered ne left right (List.range' 0 left.length)
theorem loop_binding {α β : Type} (ne : α → β → Result Bool)
    (left : List α) (right : List β) (remaining index : Nat) :
    source_loop ne left right remaining index = ordered ne left right (List.range' index remaining) := by
 induction remaining generalizing index with
 | zero => rfl
 | succ remaining ih =>
   simp only [source_loop,List.range'_succ,ordered]
   cases compare_at ne left right index with
   | fail e => rfl
   | div => rfl
   | ok different => cases different <;> simp only [Bool.false_eq_true,↓reduceIte,ih]
theorem source_binding {α β : Type} (ne : α → β → Result Bool)
    (left : List α) (right : List β) : source ne left right = model ne left right := by
 unfold source model
 split
 · rfl
 · exact loop_binding ne left right left.length 0
/-- Every source indexing operation is in range throughout the equal-length loop. -/
theorem source_read_bounds (leftLen rightLen index remaining : Nat)
    (same : leftLen = rightLen) (measure : index+remaining=leftLen)
    (step : 0<remaining) : index<leftLen ∧ index<rightLen ∧ index+1≤leftLen := by
 omega
/-- Concrete family of source slice-equality bodies, indexed by comparator. -/
theorem source_link (α β : Type) :
    PV_B3P_Link_std_dependency_closure14
      (fun _ : Unit => (α → β → Result Bool) → List α → List β → Result Bool)
      (fun _ => @source α β) (fun _ => @model α β) := by
 intro _
 funext ne left right
 exact source_binding ne left right
#print axioms loop_binding
#print axioms source_binding
#print axioms source_read_bounds
#print axioms source_link
end PV_B3Q_SliceEqual
