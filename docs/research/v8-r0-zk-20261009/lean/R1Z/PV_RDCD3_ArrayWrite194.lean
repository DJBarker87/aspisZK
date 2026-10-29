import R1Z.PV_RDCD3_Index194

namespace R1Z.PV_RDCD3_ArrayWrite194
set_option autoImplicit false
open Aeneas Aeneas.Std Result

/-- Owned state transition for the native intrinsic indexed assignment.
Invalid indices retain terminal failure rather than silently ignoring a write. -/
def write {T : Type} (xs : List T) (i : Nat) (v : T) : Result (List T) :=
  if i < xs.length then ok (xs.set i v) else fail .arrayOutOfBounds

/-- Complete emitted array writeback, projected to its entire backing storage. -/
theorem complete {T : Type} {N : Usize} (xs : Array T N) (i : Usize) (v : T) :
    write xs.val i.val v = (do let out ← Array.update xs i v; ok out.val) := by
  simp only [write,Array.update,Array.getElem?_Usize_eq]
  split
  · rename_i h
    rw [List.getElem?_eq_getElem h]
    rfl
  · rename_i h
    rw [List.getElem?_eq_none (by omega)]
    rfl

theorem success {T : Type} (xs : List T) (i : Nat) (v : T) (bound : i < xs.length) :
    write xs i v = ok (xs.set i v) := if_pos bound

theorem failure {T : Type} (xs : List T) (i : Nat) (v : T) (invalid : xs.length ≤ i) :
    write xs i v = fail .arrayOutOfBounds := if_neg (by omega)

/-- The changed position really contains the written value. -/
theorem read_back {T : Type} (xs : List T) (i : Nat) (v : T) (bound : i < xs.length) :
    (xs.set i v)[i]? = some v := by
  induction xs generalizing i with
  | nil => simp at bound
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i (by simpa using bound)

/-- Every other position is unchanged, including an out-of-bounds query. -/
theorem frame {T : Type} (xs : List T) (i j : Nat) (v : T) (different : j ≠ i) :
    (xs.set i v)[j]? = xs[j]? := by
  induction xs generalizing i j with
  | nil => simp
  | cons x xs ih =>
    cases i <;> cases j <;> simp_all [List.set]

#print axioms complete
#print axioms success
#print axioms failure
#print axioms read_back
#print axioms frame
end R1Z.PV_RDCD3_ArrayWrite194
