import Aeneas

/-! Owned checked-read law, generic in the concrete element type. The native
panic boundary is represented by arrayOutOfBounds, as in the retained Result
interface. Pointer validity and source-body binding remain separate. -/
namespace R1Z.PV_RDCD3_Index194
set_option autoImplicit false
open Aeneas Aeneas.Std Result

def read {T : Type} (xs : List T) (i : Nat) : Result T :=
  if h : i < xs.length then ok xs[i] else fail .arrayOutOfBounds

theorem slice_complete {T : Type} (xs : Slice T) (i : Usize) :
    read xs.val i.val = Slice.index_usize xs i := by
  simp only [read,Slice.index_usize,Slice.getElem?_Usize_eq]
  split
  · rename_i h
    rw [List.getElem?_eq_getElem h]
  · rename_i h
    rw [List.getElem?_eq_none (by omega)]

theorem array_complete {T : Type} {N : Usize} (xs : Array T N) (i : Usize) :
    read xs.val i.val = Array.index_usize xs i := by
  simp only [read,Array.index_usize,Array.getElem?_Usize_eq]
  split
  · rename_i h
    rw [List.getElem?_eq_getElem h]
  · rename_i h
    rw [List.getElem?_eq_none (by omega)]

theorem success {T : Type} (xs : List T) (i : Nat) (h : i < xs.length) :
    read xs i = ok xs[i] := dif_pos h

theorem failure {T : Type} (xs : List T) (i : Nat) (h : xs.length ≤ i) :
    read xs i = fail .arrayOutOfBounds := dif_neg (by omega)

/-- Bounds checks and word reads do not mutate backing storage. -/
def readFrame {T : Type} (xs : List T) (i : Nat) : Result (T × List T) := do
  let x ← read xs i
  ok (x,xs)

theorem frame {T : Type} (xs : List T) (i : Nat) (h : i < xs.length) :
    readFrame xs i = ok (xs[i],xs) := by
  rw [readFrame,success xs i h,bind_tc_ok]

/-- A failed earlier dimension read prevents later reads and the continuation. -/
theorem nested_failure {T U : Type} (xs : List T) (i : Nat)
    (h : xs.length ≤ i) (f : T → Result U) :
    (read xs i >>= f) = fail .arrayOutOfBounds := by
  rw [failure xs i h,bind_tc_fail]

/-- Full Result transport through a read, with no assumed successful callback. -/
theorem mapped {T U : Type} (xs : List T) (i : Nat) (f : T → U) :
    read (xs.map f) i = (do let x ← read xs i; ok (f x)) := by
  by_cases h : i < xs.length
  · rw [success _ i (by simpa using h),success xs i h,bind_tc_ok]
    simp only [List.getElem_map]
  · rw [failure _ i (by simpa using Nat.le_of_not_gt h),
      failure xs i (by omega),bind_tc_fail]

#print axioms slice_complete
#print axioms array_complete
#print axioms success
#print axioms failure
#print axioms frame
#print axioms nested_failure
#print axioms mapped
end R1Z.PV_RDCD3_Index194
