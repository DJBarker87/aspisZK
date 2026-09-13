import Mathlib.Logic.Equiv.Defs

/-! Whole-function transpositions. These are NOT live-oracle programming rules. -/
set_option autoImplicit false
namespace AspisV8R13
variable {Key Digest : Type*} [DecidableEq Key]

def swapCells (H : Key → Digest) (a b : Key) : Key → Digest :=
  fun x => if x = a then H b else if x = b then H a else H x

@[simp] theorem swapCells_left (H : Key → Digest) (a b : Key) :
    swapCells H a b a = H b := by simp [swapCells]

@[simp] theorem swapCells_right (H : Key → Digest) (a b : Key) :
    swapCells H a b b = H a := by
  by_cases h : b = a
  · subst b; simp [swapCells]
  · simp [swapCells, h]

@[simp] theorem swapCells_self (H : Key → Digest) (a : Key) :
    swapCells H a a = H := by
  funext x
  by_cases h : x = a <;> simp [swapCells, h]

theorem swapCells_away (H : Key → Digest) (a b x : Key)
    (ha : x ≠ a) (hb : x ≠ b) : swapCells H a b x = H x := by
  simp [swapCells, ha, hb]

@[simp] theorem swapCells_reverse (H : Key → Digest) (a b : Key) :
    swapCells (swapCells H a b) b a = H := by
  funext x
  by_cases hxa : x = a
  · subst x; simp
  · by_cases hxb : x = b
    · subst x; simp
    · simp [swapCells, hxa, hxb]

#print axioms swapCells_reverse
end AspisV8R13
