import S9CircleFactorModelV1

set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1S9CirclePointscanModelV1
open AspisR1S9FactorTableSemanticsV1 AspisR1S9CircleFactorModelV1
open AspisR1S9ConstructorV3QMMulSemanticsV1
abbrev Point := AspisR1S9ActualWeightsNewBoxNewV3.circle.SecureCirclePoint

def rowZero (point : Point) (i : Nat) : ExactQM :=
  if i=0 then 1 else if i=1 then decode point.y else if i=2 then decode point.x
  else decode point.x * decode point.y

def circleRow (point : Point) (d i : Nat) : ExactQM :=
  if d=0 then rowZero point i else coefficient (decode point.x) d i

def rowWrite (before : Table) (row : Nat) (point : Point) : Table :=
  fun k d i => if k=row ∧ d<5 then circleRow point d i else before k d i

def pointRow (z : Array Point 2#usize) (k d i : Nat) : ExactQM :=
  match z.val[k]? with
  | none => 0
  | some point => circleRow point d i

def circleScanTable (before : Table) (z : Array Point 2#usize) (stop : Nat) : Table :=
  fun k d i => if 3 ≤ k ∧ k<3+stop ∧ d<5 then pointRow z (k-3) d i else before k d i

theorem circleScan_empty (before : Table) (z : Array Point 2#usize) :
    circleScanTable before z 0 = before := by
  funext k d i
  have h : ¬(3 ≤ k ∧ k<3+0 ∧ d<5) := by omega
  exact if_neg h

theorem inner_prefix_row (before : Table) (row : Nat) (point : Point) :
    prefixTable (write before row 0 (rowZero point)) row 1 5 (decode point.x) =
      rowWrite before row point := by
  funext k d i
  by_cases hk : k=row
  · by_cases hd : d=0
    · subst k; subst d
      simp only [prefixTable, write, rowWrite, circleRow, if_pos rfl,
        Nat.not_succ_le_zero, false_and, if_false, Nat.zero_lt_succ, and_self]
    · by_cases hb : d<5
      · have hl : 1 ≤ d := by omega
        simp only [prefixTable, write, rowWrite, circleRow, hk, true_and,
          hl, hb, and_self, if_true, if_neg hd]
      · have hn : ¬(1 ≤ d ∧ d<5) := by omega
        simp only [prefixTable, write, rowWrite, hk, true_and, if_neg hn,
          if_neg hd, if_neg hb]
  · have hn : ¬(k=row ∧ 1 ≤ d ∧ d<5) := by omega
    have hn' : ¬(k=row ∧ d<5) := by omega
    simp only [prefixTable, write, rowWrite, if_neg hn, if_neg hk, if_neg hn']

theorem circleScan_step (before : Table) (z : Array Point 2#usize)
    (start : Nat) (point : Point) (hpoint : z.val[start]?=some point) :
    rowWrite (circleScanTable before z start) (3+start) point =
      circleScanTable before z (start+1) := by
  funext k d i
  by_cases hk : k=3+start
  · by_cases hd : d<5
    · have hnew : 3 ≤ k ∧ k<3+(start+1) ∧ d<5 := by omega
      have hidx : k-3=start := by omega
      simp only [rowWrite, hk, hd, and_self, if_true, circleScanTable,
        if_pos hnew, pointRow, hidx, hpoint]
    · have hn : ¬(k=3+start ∧ d<5) := by omega
      have ho : ¬(3 ≤ k ∧ k<3+start ∧ d<5) := by omega
      have hn' : ¬(3 ≤ k ∧ k<3+(start+1) ∧ d<5) := by omega
      simp only [rowWrite, circleScanTable, if_neg hn, if_neg ho, if_neg hn']
  · have hn : ¬(k=3+start ∧ d<5) := by omega
    have he : (3 ≤ k ∧ k<3+(start+1) ∧ d<5) ↔ (3 ≤ k ∧ k<3+start ∧ d<5) := by omega
    simp only [rowWrite, if_neg hn, circleScanTable, he]

theorem circleScan_statement_frame (before : Table) (z : Array Point 2#usize)
    (stop k d i : Nat) (hk : k<3) : circleScanTable before z stop k d i = before k d i := by
  have hn : ¬(3 ≤ k ∧ k<3+stop ∧ d<5) := by omega
  exact if_neg hn

#print axioms circleScan_empty
#print axioms inner_prefix_row
#print axioms circleScan_step
#print axioms circleScan_statement_frame
end AspisR1S9CirclePointscanModelV1
