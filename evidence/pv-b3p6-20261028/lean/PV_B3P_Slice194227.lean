import Aeneas.Std
namespace PV_B3P_Slice194227
open Aeneas Aeneas.Std
set_option autoImplicit false

/-- Source-shaped forward loop: the first unequal element returns false.
`remaining` is the termination measure len-idx, not a Rust input or bound. -/
def indexed {α β : Type} (ne : α → β → Result Bool)
    (left : Nat → α) (right : Nat → β) : Nat → Nat → Result Bool
  | 0, _ => .ok true
  | remaining+1, idx => do
    let different ← ne (left idx) (right idx)
    if different then .ok false else indexed ne left right remaining (idx+1)

/-- The deployed 1.94.1 generic SlicePartialEq::equal length guard. -/
def deployed {α β : Type} (ne : α → β → Result Bool)
    (left : Nat → α) (right : Nat → β) (leftLen rightLen : Nat) : Result Bool :=
  if leftLen != rightLen then .ok false else indexed ne left right leftLen 0

/-- Ordered pointwise comparison specification, with all Result tags retained. -/
def compareIndices {α β : Type} (ne : α → β → Result Bool)
    (left : Nat → α) (right : Nat → β) : List Nat → Result Bool
  | [] => .ok true
  | idx::rest => do
    let different ← ne (left idx) (right idx)
    if different then .ok false else compareIndices ne left right rest

theorem indexed_result {α β : Type} (ne : α → β → Result Bool)
    (left : Nat → α) (right : Nat → β) (remaining start : Nat) :
    indexed ne left right remaining start =
      compareIndices ne left right (List.range' start remaining) := by
  induction remaining generalizing start with
  | zero => rfl
  | succ remaining ih =>
    simp only [indexed,List.range'_succ,compareIndices]
    cases ne (left start) (right start) with
    | fail e => rfl
    | div => rfl
    | ok different => cases different <;> simp only [Bool.false_eq_true,↓reduceIte,ih]

theorem complete_result {α β : Type} (ne : α → β → Result Bool)
    (left : Nat → α) (right : Nat → β) (leftLen rightLen : Nat) :
    deployed ne left right leftLen rightLen =
      if leftLen = rightLen then compareIndices ne left right (List.range' 0 leftLen)
      else .ok false := by
  by_cases h : leftLen=rightLen
  · simp only [deployed,h,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,indexed_result]
  · simp only [deployed,bne_iff_ne,ne_eq,h,not_false_eq_true,↓reduceIte]

theorem same_length {α β : Type} (ne : α → β → Result Bool)
    (left : Nat → α) (right : Nat → β) (len : Nat) :
    deployed ne left right len len = indexed ne left right len 0 := by
  simp only [deployed,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]

theorem different_length {α β : Type} (ne : α → β → Result Bool)
    (left : Nat → α) (right : Nat → β) (leftLen rightLen : Nat)
    (h : leftLen ≠ rightLen) : deployed ne left right leftLen rightLen = .ok false := by
  simp only [deployed,bne_iff_ne,ne_eq,h,not_false_eq_true,↓reduceIte]

#print axioms indexed_result
#print axioms complete_result
#print axioms same_length
#print axioms different_length
end PV_B3P_Slice194227
