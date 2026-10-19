import RRFiniteCoeffScannerV9

namespace RRInitialFullRowsScanFacts

variable {K : Type} [Zero K] [DecidableEq K]

private def isZeroRow (row : List K) : Bool :=
  RRFiniteCoeffScannerV9.rowNonzeroFull row == false

theorem firstNonzeroFullRows_none_iff_allZero (xs : List (List K)) :
    RRFiniteCoeffScannerV9.firstNonzeroFullRows xs = none ↔
      xs.all isZeroRow = true := by
  induction xs with
  | nil => simp [RRFiniteCoeffScannerV9.firstNonzeroFullRows]
  | cons row rows ih =>
      by_cases hrow : RRFiniteCoeffScannerV9.rowNonzeroFull row = true
      · simp [RRFiniteCoeffScannerV9.firstNonzeroFullRows, hrow, isZeroRow]
      · have hrowF : RRFiniteCoeffScannerV9.rowNonzeroFull row = false :=
          Bool.eq_false_of_not_eq_true hrow
        simp [RRFiniteCoeffScannerV9.firstNonzeroFullRows, hrowF, isZeroRow, ih]

theorem firstNonzeroFullRows_some_decompose
    (xs : List (List K)) (v : Nat) (row : List K)
    (hscan : RRFiniteCoeffScannerV9.firstNonzeroFullRows xs = some (v,row)) :
    ∃ pre post, xs = pre ++ row :: post ∧ pre.length = v ∧
      pre.all isZeroRow = true ∧
      RRFiniteCoeffScannerV9.rowNonzeroFull row = true := by
  induction xs generalizing v row with
  | nil => simp [RRFiniteCoeffScannerV9.firstNonzeroFullRows] at hscan
  | cons head tail ih =>
      by_cases hhead : RRFiniteCoeffScannerV9.rowNonzeroFull head = true
      · simp [RRFiniteCoeffScannerV9.firstNonzeroFullRows, hhead] at hscan
        rcases hscan with ⟨rfl, rfl⟩
        exact ⟨[], tail, by simp, by simp, by simp [isZeroRow], hhead⟩
      · have hheadF : RRFiniteCoeffScannerV9.rowNonzeroFull head = false :=
          Bool.eq_false_of_not_eq_true hhead
        cases htail : RRFiniteCoeffScannerV9.firstNonzeroFullRows tail with
        | none => simp [RRFiniteCoeffScannerV9.firstNonzeroFullRows, hheadF, htail] at hscan
        | some pair =>
            rcases pair with ⟨v', row'⟩
            have hrec := ih v' row' htail
            obtain ⟨pre, post, hxs, hlen, hzeros, hrow⟩ := hrec
            have hvals : v'+1 = v ∧ row' = row := by
              simpa [RRFiniteCoeffScannerV9.firstNonzeroFullRows, hheadF, htail] using hscan
            rcases hvals with ⟨rfl, rfl⟩
            refine ⟨head :: pre, post, ?_, ?_, ?_, hrow⟩
            · simp [hxs, List.cons_append]
            · simp [hlen]
            · simp [isZeroRow, hheadF, hzeros]

#print axioms firstNonzeroFullRows_none_iff_allZero
#print axioms firstNonzeroFullRows_some_decompose

end RRInitialFullRowsScanFacts
