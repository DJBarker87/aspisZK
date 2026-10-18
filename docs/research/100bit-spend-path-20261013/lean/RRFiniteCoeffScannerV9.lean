import Mathlib.Data.ZMod.Basic

namespace RRFiniteCoeffScannerV9
variable {K : Type*} [Zero K] [DecidableEq K]

def firstNonzeroWithCost : List K → Nat × Option Nat
  | [] => (0, none)
  | x :: xs =>
      if x ≠ 0 then (1, some 0)
      else
        let (c, r) := firstNonzeroWithCost xs
        (c + 1, r.map Nat.succ)

theorem firstNonzeroWithCost_tests_le_length (xs : List K) :
    (firstNonzeroWithCost xs).1 ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x ≠ 0
      · simp [firstNonzeroWithCost, hx]
      · simp [firstNonzeroWithCost, hx]
        omega

def rowNonzeroFull : List K → Bool
  | [] => false
  | x :: xs =>
      let later := rowNonzeroFull xs
      (x != 0) || later

theorem rowNonzeroFull_eq_any (row : List K) :
    rowNonzeroFull row = row.any (fun x => x != 0) := by
  induction row with
  | nil => rfl
  | cons x xs ih => simp [rowNonzeroFull, List.any_cons, ih]

def firstNonzeroFullRows : List (List K) → Option (Nat × List K)
  | [] => none
  | row :: rows =>
      let later := firstNonzeroFullRows rows
      if rowNonzeroFull row then some (0, row)
      else later.map (fun (i, r) => (i + 1, r))

def firstNonzeroAnyRows : List (List K) → Option (Nat × List K)
  | [] => none
  | row :: rows =>
      if row.any (fun x => x != 0) then some (0, row)
      else (firstNonzeroAnyRows rows).map (fun (i, r) => (i + 1, r))

theorem firstNonzeroFullRows_eq_firstNonzeroAnyRows (rows : List (List K)) :
    firstNonzeroFullRows rows = firstNonzeroAnyRows rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [firstNonzeroFullRows, firstNonzeroAnyRows, rowNonzeroFull_eq_any, ih]

#eval firstNonzeroWithCost ([0, 0, 1, 2] : List (ZMod 3))
#eval firstNonzeroFullRows ([[0,0,0], [0,1,2], [4]] : List (List (ZMod 7)))
#print axioms firstNonzeroWithCost
#print axioms rowNonzeroFull
#print axioms firstNonzeroFullRows
#print axioms firstNonzeroFullRows_eq_firstNonzeroAnyRows
end RRFiniteCoeffScannerV9
