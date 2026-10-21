import AllocationBatchM10
import AllocationFoldM10
import GSInterpolationFullWorkM10

/-! Matrix, kernel, and normalization allocation counters. Hasse arithmetic
uses the public degree cap; polynomial additions reserve a coefficient square.
The kernel uses its existing cumulative backing-copy counter, not its work
counter. These constructor tariffs are independent of coefficient values. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InterpolationAllocationM10
open CompPoly CompPoly.GuruswamiSudan
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]

def hasseCells (D : Nat) : Nat := 10*(2^(D+1)+D+1)^2

omit [BEq K] [LawfulBEq K] [DecidableEq K] in
theorem hasse_paid (D : Nat) (m : CBivariate.Monomial) (c : InterpolationConstraint K) :
    hasseCells D ≤ (GSInterpolationMatrixWorkM10.hasse D m c).2 := by
  change 10*_ ≤ 100*_
  exact Nat.mul_le_mul_right _ (by decide : 10 ≤ 100)

def matrixCells (D : Nat) (basis : Array CBivariate.Monomial) (points : Array (K × K)) : Nat :=
  let cs := GSInterpolationMatrixWorkM10.constraints points
  let n := cs.1.size*basis.size
  20*(points.size+1)^2+AllocationBatchM10.cells (fun _ : Fin n => hasseCells D)+3*n+1

theorem matrix_paid (D : Nat) (basis : Array CBivariate.Monomial) (points : Array (K × K)) :
    matrixCells D basis points ≤ (GSInterpolationMatrixWorkM10.matrix D basis points).2 := by
  have hc : 20*(points.size+1)^2 ≤ (GSInterpolationMatrixWorkM10.constraints points).2 :=
    Nat.mul_le_mul_right _ (by decide : 20 ≤ 100)
  have hb := AllocationBatchM10.batch_work
    (fun i : Fin ((GSInterpolationMatrixWorkM10.constraints points).1.size*basis.size) =>
      GSInterpolationMatrixWorkM10.hasse D (basis.getD (i.val%basis.size) ⟨0,0⟩)
        ((GSInterpolationMatrixWorkM10.constraints points).1.getD (i.val/basis.size) ⟨0,0,0,0⟩))
    (fun _ => hasseCells D) (fun _ => hasse_paid _ _ _)
  change _+_+_+1 ≤ _+_+_+1
  nlinarith

def vectorCells (v : Array K) : Nat :=
  let found := DenseMatrix.findCounted (fun i => !(v.getD i 0 == 0)) (List.range v.size)
  found.2+2*v.size+2

omit [LawfulBEq K] [DecidableEq K] in
theorem vector_paid (v : Array K) : vectorCells v ≤ (GSInterpolationNormalizationWorkM10.vector v).2 := by
  change _+2*v.size+2 ≤ _+4*v.size+4
  omega

def addCells (D : Nat) : Nat := 10*(D+1)^2

def polynomialCells (D : Nat) (basis : Array CBivariate.Monomial) (cs : Array K) : Nat :=
  AllocationFoldM10.cells
    (fun out col =>
      let m := basis.getD col ⟨0,0⟩
      (out+CBivariate.monomialXY m.xDegree m.yDegree (cs.getD col 0),
        GSInterpolationNormalizationWorkM10.addTariff D))
    (fun _ _ => addCells D) 0 (List.range' 0 basis.size)

theorem polynomial_paid (D : Nat) (basis : Array CBivariate.Monomial) (cs : Array K) :
    polynomialCells D basis cs ≤ (GSInterpolationNormalizationWorkM10.polynomial D basis cs).2 := by
  apply AllocationFoldM10.work
  intro out col
  change 10*_ ≤ 100*_
  exact Nat.mul_le_mul_right _ (by decide : 10 ≤ 100)

def normalizeCells (D : Nat) (basis : Array CBivariate.Monomial) (cs : Array K) : Nat :=
  vectorCells cs+(match (GSInterpolationNormalizationWorkM10.vector cs).1 with
    | none => 0 | some w => polynomialCells D basis w)+1

theorem normalize_paid (D : Nat) (basis : Array CBivariate.Monomial) (cs : Array K) :
    normalizeCells D basis cs ≤ (GSInterpolationNormalizationWorkM10.normalize D basis cs).2 := by
  have hv := vector_paid cs
  cases h : (GSInterpolationNormalizationWorkM10.vector cs).1 with
  | none => simp only [normalizeCells,GSInterpolationNormalizationWorkM10.normalize,h]; omega
  | some w =>
    have hp := polynomial_paid D basis w
    simp only [normalizeCells,GSInterpolationNormalizationWorkM10.normalize,h]
    omega

def cells (D : Nat) (basis : Array CBivariate.Monomial) (points : Array (K × K)) : Nat :=
  let M := GSInterpolationMatrixWorkM10.matrix D basis points
  let k := GSDenseKernelResourcesM10.eval M.1
  matrixCells D basis points+k.2.allocated+1+
    (match k.1 with | none => 0 | some v => normalizeCells D basis v)

theorem paid (D : Nat) (basis : Array CBivariate.Monomial) (points : Array (K × K)) :
    cells D basis points ≤ (GSInterpolationFullWorkM10.eval D basis points).2 := by
  have hm := matrix_paid D basis points
  cases h : (GSDenseKernelResourcesM10.eval (GSInterpolationMatrixWorkM10.matrix D basis points).1).1 with
  | none => simp only [cells,GSInterpolationFullWorkM10.eval,h]; omega
  | some v =>
    have hn := normalize_paid D basis v
    simp only [cells,GSInterpolationFullWorkM10.eval,h]
    omega

#print axioms hasse_paid
#print axioms matrix_paid
#print axioms vector_paid
#print axioms polynomial_paid
#print axioms normalize_paid
#print axioms paid
end AspisR1.InterpolationAllocationM10
end
