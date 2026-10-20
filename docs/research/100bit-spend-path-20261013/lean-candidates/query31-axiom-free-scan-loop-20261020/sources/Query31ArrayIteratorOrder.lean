import Query31ExplicitListLoop
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace Query31ArrayIteratorOrder
open Query31ExplicitListLoop AspisV8R19.Q22WordScan

def arrayIteratorModel {n : Usize} (a : Array Std.U32 n) : List Std.U32 := a.val

def pullN : Nat → List Std.U32 → List Std.U32 × List Std.U32
  | 0, xs => ([], xs)
  | n + 1, [] => ([], [])
  | n + 1, x :: xs =>
      let (out, rest) := pullN n xs
      (x :: out, rest)

theorem pullN_is_take_drop (n : Nat) (xs : List Std.U32) :
    pullN n xs = (xs.take n, xs.drop n) := by
  induction n generalizing xs with
  | zero => simp [pullN]
  | succ n ih =>
      cases xs with
      | nil => simp [pullN]
      | cons x xs =>
          simp only [pullN]
          rw [ih]
          simp

theorem arrayIteratorModel_order {n : Usize} (a : Array Std.U32 n)
    (k : Nat) :
    pullN k (arrayIteratorModel a) = (a.val.take k, a.val.drop k) := by
  exact pullN_is_take_drop k a.val

theorem arrayIteratorModel_next_empty {n : Usize} (a : Array Std.U32 n)
    (h : arrayIteratorModel a = []) :
    listNext (arrayIteratorModel a) = .ok (none, []) := by
  simp [listNext, h]

theorem arrayIteratorModel_next_cons {n : Usize} (a : Array Std.U32 n)
    (x : Std.U32) (xs : List Std.U32)
    (h : arrayIteratorModel a = x :: xs) :
    listNext (arrayIteratorModel a) = .ok (some x, xs) := by
  simp [listNext, h]

/-- The source-shaped scan body on the explicit array-order iterator model
    refines Q22 for the array's ordered values. This is a model result; it does
    not import the generated external IntoIter axioms. -/
theorem array_scan_q22 {n : Usize} (a : Array Std.U32 n)
    (s : CurrentScan) (hs : validState s) :
    ∃ sf pending,
      scanListLoop (arrayIteratorModel a) s = .ok (sf, pending) ∧
      scan (Query31ExplicitScanBody.q22StateOf s) (a.val.map (fun x => x.val)) =
        (Query31ExplicitScanBody.q22StateOf sf, optionStop pending) := by
  simpa [arrayIteratorModel] using scanListLoop_q22 a.val s hs

#print axioms pullN_is_take_drop
#print axioms arrayIteratorModel_order
#print axioms array_scan_q22
end Query31ArrayIteratorOrder
