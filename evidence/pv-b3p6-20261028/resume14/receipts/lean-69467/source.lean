import PV_B3P_TransitionLoan14227
namespace PV_B3P_Loans14227
open Aeneas Aeneas.Std Result
set_option autoImplicit false
/-- One immutable non-ZST slice region. Addresses are region/element tokens;
this is not a pointer-to-integer cast. Intrinsic realization stays at V370. -/
structure ImmutableCursor14 (α : Type) where
  region : Nat
  consumed : List α
  remaining : List α

def cursor_start14 {α : Type} (cursor : ImmutableCursor14 α) : Nat := cursor.consumed.length
def cursor_end14 {α : Type} (cursor : ImmutableCursor14 α) : Nat :=
  cursor.consumed.length + cursor.remaining.length

def cursor_new14 {α : Type} (region : Nat) (values : List α) : ImmutableCursor14 α :=
  ⟨region,[],values⟩

def cursor_next14 {α : Type} (cursor : ImmutableCursor14 α) :
    Option (Shared14 α) × ImmutableCursor14 α :=
  match cursor.remaining with
  | [] => (none,cursor)
  | value::rest =>
    (some ⟨Nat.pair cursor.region (cursor_start14 cursor),value⟩,
     ⟨cursor.region,cursor.consumed++[value],rest⟩)

theorem cursor_end_iff_empty14 {α : Type} (cursor : ImmutableCursor14 α) :
    cursor_start14 cursor = cursor_end14 cursor ↔ cursor.remaining = [] := by
  simp only [cursor_start14,cursor_end14,Nat.left_eq_add,List.length_eq_zero_iff]

theorem cursor_new_source14 {α : Type} (region : Nat) (values : List α) :
    cursor_start14 (cursor_new14 region values) = 0 ∧
    cursor_end14 (cursor_new14 region values) = values.length := by
  constructor <;> rfl

theorem cursor_forward_source14 {α : Type} (region : Nat) (prefix : List α)
    (value : α) (rest : List α) :
    cursor_next14 (⟨region,prefix,value::rest⟩ : ImmutableCursor14 α) =
      (some ⟨Nat.pair region prefix.length,value⟩,⟨region,prefix++[value],rest⟩) := rfl

theorem cursor_advance14 {α : Type} (region : Nat) (prefix : List α)
    (value : α) (rest : List α) :
    cursor_start14 (⟨region,prefix++[value],rest⟩ : ImmutableCursor14 α) =
      cursor_start14 (⟨region,prefix,value::rest⟩ : ImmutableCursor14 α) + 1 := by
  simp only [cursor_start14,List.length_append,List.length_singleton]

theorem cursor_backing_preserved14 {α : Type} (prefix : List α) (value : α) (rest : List α) :
    (prefix++[value])++rest = prefix++(value::rest) := by
  simp only [List.append_assoc,List.singleton_append]
#print axioms cursor_end_iff_empty14
#print axioms cursor_new_source14
#print axioms cursor_forward_source14
#print axioms cursor_advance14
#print axioms cursor_backing_preserved14
end PV_B3P_Loans14227
