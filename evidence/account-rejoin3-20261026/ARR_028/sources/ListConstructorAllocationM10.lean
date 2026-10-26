import AllocationStageSpecM10
import BinLeafListWork

/-! Source-site counters for transient list operations. A counted cell is a
fixed-width constructor/result group; referenced payloads are not deep copied.
The instrumentation's own proof/counter values are erased from the model. -/
set_option autoImplicit false
namespace AspisR1.ListConstructorAllocationM10

def takeCells {A : Type} : Nat → List A → Nat
  | 0, _ => 1
  | _+1, [] => 1
  | n+1, _::xs => takeCells n xs+2

def dropCells {A : Type} : Nat → List A → Nat
  | 0, _ => 1
  | _+1, [] => 1
  | n+1, _::xs => dropCells n xs+1

def appendCells {A : Type} : List A → Nat
  | [] => 1
  | _::xs => appendCells xs+2

def equalCells : List BinMerkle32Path.Byte → List BinMerkle32Path.Byte → Nat
  | [], _ => 1
  | _::_, [] => 1
  | x::xs, y::ys => if x = y then equalCells xs ys+1 else 1

theorem take_work {A : Type} (n : Nat) (xs : List A) :
    takeCells n xs ≤ (BinLeafListWork.take n xs).2 := by
  induction n generalizing xs with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    cases xs with
    | nil => exact Nat.le_refl _
    | cons x xs => exact Nat.add_le_add_right (ih xs) 2

theorem drop_work {A : Type} (n : Nat) (xs : List A) :
    dropCells n xs ≤ (BinLeafListWork.drop n xs).2 := by
  induction n generalizing xs with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    cases xs with
    | nil => exact Nat.le_refl _
    | cons x xs => exact Nat.add_le_add_right (ih xs) 1

theorem append_work {A : Type} (xs ys : List A) :
    appendCells xs ≤ (BinLeafListWork.append xs ys).2 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.add_le_add_right ih 2

theorem equal_work (xs ys : List BinMerkle32Path.Byte) :
    equalCells xs ys ≤ (BinLeafListWork.equal xs ys).2 := by
  induction xs generalizing ys with
  | nil => cases ys <;> exact Nat.le_refl _
  | cons x xs ih =>
    cases ys with
    | nil => exact Nat.le_refl _
    | cons y ys =>
      have ht := ih ys
      simp only [equalCells,BinLeafListWork.equal]
      split <;> omega

/-- A concrete, nonempty prefix copies two cons cells and its result group. -/
theorem nonvacuous : takeCells 2 ([1,2,3] : List Nat) = 5 := rfl

#print axioms take_work
#print axioms drop_work
#print axioms append_work
#print axioms equal_work
#print axioms nonvacuous
end AspisR1.ListConstructorAllocationM10
