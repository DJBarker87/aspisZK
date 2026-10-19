import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import Mathlib.Data.Finset.Basic

open CompPoly
open CompPoly.CBivariate
open CompPoly.GuruswamiSudan

namespace AspisWide.GSInterpolationRowBasis

/-- The `j`th row of the weighted-degree triangle, in increasing `X` degree. -/
def row (d D j : Nat) : List CBivariate.Monomial :=
  (List.range (D + 1 - d * j)).map fun i => ⟨i, j⟩

/-- An executable row-by-row enumeration; it avoids filtering the full square grid. -/
def rows (d D ell : Nat) : List CBivariate.Monomial :=
  (List.range (ell + 1)).flatMap (row d D)

def basis (d D ell : Nat) : Array CBivariate.Monomial := (rows d D ell).toArray

def rowCount (d D ell : Nat) : Nat :=
  (Finset.range (ell + 1)).sum fun j => D + 1 - d * j

/-- The triangular count convention used in the maintained GS budget. -/
def weightedMonomialCount (d D ell : Nat) : Nat :=
  (Finset.range (ell + 1)).sum fun j => D - d * j + 1

theorem rowCount_eq_weightedMonomialCount (d D ell : Nat) (htri : d * ell ≤ D) :
    rowCount d D ell = weightedMonomialCount d D ell := by
  unfold rowCount weightedMonomialCount
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ ell := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdj : d * j ≤ D := Nat.le_trans (Nat.mul_le_mul_left d hjle) htri
  omega

theorem list_range_sum_eq_finset_sum (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [List.range_succ, ih, Finset.sum_range_succ]

theorem row_length (d D j : Nat) : (row d D j).length = D + 1 - d * j := by
  simp [row]

theorem rows_length_eq_rowCount (d D ell : Nat) :
    (rows d D ell).length = rowCount d D ell := by
  rw [rows, List.length_flatMap]
  simp only [row_length, rowCount]
  exact list_range_sum_eq_finset_sum (ell + 1) (fun j => D + 1 - d * j)

private theorem row_pairwise (d D j : Nat) :
    List.Pairwise (fun a b : CBivariate.Monomial => a ≠ b) (row d D j) := by
  exact List.Pairwise.map
    (f := fun i => (⟨i, j⟩ : CBivariate.Monomial))
    (by
      intro a b hab heq
      exact hab (congrArg CBivariate.Monomial.xDegree heq))
    ((List.nodup_iff_pairwise_ne.mp (List.nodup_range (n := D + 1 - d * j))))

private theorem rows_disjoint (d D ell : Nat) :
    List.Pairwise
      (fun a b : Nat => ∀ x ∈ row d D a, ∀ y ∈ row d D b, (x : CBivariate.Monomial) ≠ y)
      (List.range (ell + 1)) := by
  apply List.Pairwise.imp (R := fun a b : Nat => a ≠ b)
    (S := fun a b : Nat =>
      ∀ x ∈ row d D a, ∀ y ∈ row d D b, (x : CBivariate.Monomial) ≠ y)
  · intro j k hjk x hx y hy hxy
    have hxj : x.yDegree = j := by
      rcases List.mem_map.mp hx with ⟨i, hi, hxi⟩
      rw [← hxi]
    have hyk : y.yDegree = k := by
      rcases List.mem_map.mp hy with ⟨i, hi, hyi⟩
      rw [← hyi]
    have hxyDegree := congrArg CBivariate.Monomial.yDegree hxy
    exact hjk (hxj.symm.trans (hxyDegree.trans hyk))
  · exact (List.nodup_iff_pairwise_ne.mp (List.nodup_range (n := ell + 1)))

theorem rows_nodup (d D ell : Nat) : (rows d D ell).Nodup := by
  change List.Nodup ((List.range (ell + 1)).flatMap (row d D))
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  constructor
  · intro j hj
    exact row_pairwise d D j
  · exact rows_disjoint d D ell

theorem basis_nodup (d D ell : Nat) : (basis d D ell).toList.Nodup := by
  simpa [basis] using rows_nodup d D ell

theorem row_weighted_bound (d D ell : Nat) (htri : d * ell ≤ D)
    {m : CBivariate.Monomial} (hm : m ∈ rows d D ell) :
    m.xDegree + d * m.yDegree ≤ D := by
  rcases List.mem_flatMap.mp hm with ⟨j, hj, hrow⟩
  rcases List.mem_map.mp hrow with ⟨i, hi, hmi⟩
  subst m
  have hjle : j ≤ ell := by
    exact Nat.lt_succ_iff.mp (List.mem_range.mp hj)
  have hdj : d * j ≤ D := Nat.le_trans (Nat.mul_le_mul_left d hjle) htri
  have hi_lt : i < D + 1 - d * j := List.mem_range.mp hi
  change i + d * j ≤ D
  omega

theorem basis_size (d D ell : Nat) : (basis d D ell).size = rowCount d D ell := by
  simp [basis, rows_length_eq_rowCount]

end AspisWide.GSInterpolationRowBasis
