import AllocationFoldM10
import TypedCacheAllocationM10
import RecoveryParserAllocationM10
import RRNormalizationWorkM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.RRRowAllocationM10
open CompPoly RRConcreteState
variable {K : Type} [Field K] [DecidableEq K]

def termCells (D : Nat) : Nat := 10*(2^(D+1)+D+1)^2

def taylorCells (D : Nat) (cs : List K) (a : K) (j : Nat) : Nat :=
  AllocationFoldM10.cells
    (fun (total : K) i =>
      (total+(if j ≤ i then (i.choose j : K)*RRDenseCoeffVector.coeffAt cs i*a^(i-j) else 0),
        RRRowConstructionWorkM10.termTariff D))
    (fun _ _ => termCells D) 0 (List.range cs.length)+cs.length+1

theorem taylor_paid (D : Nat) (cs : List K) (a : K) (j : Nat) :
    taylorCells D cs a j ≤ (RRRowConstructionWorkM10.taylor D cs a j).2 := by
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply AllocationFoldM10.work
  intro s i
  change 10*_ ≤ 100*_
  exact Nat.mul_le_mul_right _ (by decide : 10 ≤ 100)

def valueCells (D : Nat) (gs : List (List K)) (a : K) (M n j : Nat) : Nat :=
  if j ≤ n then if n-j ≤ M then
    TypedCacheAllocationM10.lookupCells gs (n-j)+
      taylorCells D ((BinTypedCacheWork.lookup gs (n-j)).1.getD []) a j+2
  else 2 else 2

theorem value_paid (D : Nat) (gs : List (List K)) (a : K) (M n j : Nat) :
    valueCells D gs a M n j ≤ (RRRowConstructionWorkM10.valueAt D gs a M n j).2 := by
  have hl := TypedCacheAllocationM10.lookup_work gs (n-j)
  have ht := taylor_paid D ((BinTypedCacheWork.lookup gs (n-j)).1.getD []) a j
  simp only [valueCells,RRRowConstructionWorkM10.valueAt]
  split
  · split <;> omega
  · omega

def rowCells (D : Nat) (gs : List (List K)) (a : K) (M n : Nat) : Nat :=
  ((List.finRange (n+1)).map (fun j => valueCells D gs a M n j.val)).sum+n+2

theorem row_paid (D : Nat) (gs : List (List K)) (a : K) (M n : Nat) :
    rowCells D gs a M n ≤ (RRRowConstructionWorkM10.row D gs a M n).2 := by
  have hs := RecoveryParserAllocationM10.sum_mono (List.finRange (n+1))
    (fun j => valueCells D gs a M n j.val)
    (fun j => (RRRowConstructionWorkM10.valueAt D gs a M n j.val).2)
    (fun j _ => value_paid _ _ _ _ _ _)
  simpa only [rowCells,RRRowConstructionWorkM10.row,List.map_map,Function.comp_def] using
    Nat.add_le_add_right (Nat.add_le_add_right hs n) 2

def rowsCells (D : Nat) (gs : List (List K)) (a : K) (M B : Nat) : Nat :=
  ((List.finRange (B+1)).map (fun n => rowCells D gs a M n.val)).sum+3*(B+1)+1

theorem rows_paid (D : Nat) (gs : List (List K)) (a : K) (M B : Nat) :
    rowsCells D gs a M B ≤ (RRNormalizationWorkM10.rows D gs a M B).2 := by
  have hs := RecoveryParserAllocationM10.sum_mono (List.finRange (B+1))
    (fun n => rowCells D gs a M n.val)
    (fun n => (RRRowConstructionWorkM10.row D gs a M n.val).2)
    (fun n _ => row_paid _ _ _ _ _)
  simpa only [rowsCells,RRNormalizationWorkM10.rows,List.map_map,Function.comp_def] using
    Nat.add_le_add_right (Nat.add_le_add_right hs (3*(B+1))) 1

def scanCells : List (List K) → Nat
  | [] => 1
  | row::rest => scanCells rest+row.length+2

theorem scan_paid (gs : List (List K)) : scanCells gs ≤ (RRNormalizationWorkM10.scan gs).2 := by
  induction gs with
  | nil => exact Nat.le_refl _
  | cons row rest ih => change _+row.length+2 ≤ _+row.length+3; omega

/-- The drop in normalized reconstruction borrows a suffix; newly created
row grids and option/state/result groups are counted separately. -/
def normalizeCells (D ell : Nat) (s : RawState K) (a : K) : Nat :=
  let grid := RRNormalizationWorkM10.rows D s.rows a s.maxX ell
  rowsCells D s.rows a s.maxX ell+scanCells grid.1+
    (match (RRNormalizationWorkM10.scan grid.1).1 with
    | none => 0 | some _ => rowsCells D s.rows a s.maxX (s.maxX+ell))+2

theorem normalize_paid (D ell : Nat) (s : RawState K) (a : K) :
    normalizeCells D ell s a+1 ≤ (RRNormalizationWorkM10.normalize D ell s a).2 := by
  have hg := rows_paid D s.rows a s.maxX ell
  have hs := scan_paid (RRNormalizationWorkM10.rows D s.rows a s.maxX ell).1
  have hf := rows_paid D s.rows a s.maxX (s.maxX+ell)
  cases h : (RRNormalizationWorkM10.scan (RRNormalizationWorkM10.rows D s.rows a s.maxX ell).1).1 with
  | none => simp only [normalizeCells,RRNormalizationWorkM10.normalize,h]; omega
  | some p =>
    rcases p with ⟨v,row⟩
    simp only [normalizeCells,RRNormalizationWorkM10.normalize,h]
    omega

#print axioms taylor_paid
#print axioms value_paid
#print axioms row_paid
#print axioms rows_paid
#print axioms scan_paid
#print axioms normalize_paid
end AspisR1.RRRowAllocationM10
end
