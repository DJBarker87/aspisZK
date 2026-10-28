import NBF_Accumulate
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_RowShape
open AspisR1 AspisR1Stage2
open S7Kani2OwnedRowRefinement (makeRow)
def coordinates (row : NBF_Frame.Row) (k : Fin 4) : U64 :=
 row.val[k.val]'(by simpa [row.property] using k.isLt)

theorem rebuild (row : NBF_Frame.Row) : makeRow (coordinates row)=row := by
 apply Subtype.ext
 apply List.ext_getElem
 · simp [makeRow,Array.make,row.property]
 · intro i h1 h2
   have len : row.val.length=4 := row.property
   have hi : i<4 := by omega
   interval_cases i <;> rfl

/-- Recover the next query's cursor0 progress from exact same-carrier phase
bounds and term count. No successful row call/next progress is assumed. -/
theorem progress (b : verifier.BatchedWeights) (t : Nat)
 (terms : b.terms.val=t) (size : b.raw.val.length=64)
 (phase : ∀ (j : Nat) (row : NBF_Frame.Row), b.raw.val[j]?=some row → NBB_Sweep.Bound t row) :
 S7JoinRowsTrace.Progress t 0 (Port3_RowsInstall.toBW b) := by
 refine ⟨terms,size,?_⟩
 intro j bound
 have hindex : j<b.raw.val.length := by omega
 let row := b.raw.val[j]
 have get : b.raw.val[j]?=some row := by rw [List.getElem?_eq_getElem hindex]
 refine ⟨coordinates row,?_,?_⟩
 · change b.raw.val[j]?=some (makeRow (coordinates row))
   rw [rebuild];exact get
 · intro k
   have word := phase j row get (coordinates row k) (List.getElem_mem _)
   simpa only [Nat.not_lt_zero,if_false,NBB_Phase.Bound,S7Kani3PhaseInvariant.Phase,
     AspisR1BatchedFoldSourceStep.productCap] using word
#print axioms rebuild
#print axioms progress
end NBF_RowShape
