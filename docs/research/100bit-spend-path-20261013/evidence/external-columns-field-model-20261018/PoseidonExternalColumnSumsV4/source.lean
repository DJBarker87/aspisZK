import PoseidonExternalColumnArrayCallV3
import ArrayFromFnCopyStable
import AspisR1.PoseidonFullRoundCellStep

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalColumnSums
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalColumnArrayCall
open AspisR1.PoseidonExternalColumnCall
open AspisR1.PoseidonFullRoundCellStep

abbrev State := Array field.QM31 16#usize
abbrev U32 := Std.U32
abbrev U64 := Std.U64
abbrev Row := Array U64 4#usize
abbrev Sums := Array Row 4#usize

/-- Read one concrete U64 from the generated four-column sum table. -/
def sumWordAt (sums : Sums) (i j : Fin 4) : U64 := cell (cell sums i) j

private theorem column_output_bound (state : State) (column : Usize)
    (hcolumn : column.val < 4) (j : Fin 4) (v : U64)
    (hv : columnTotal state column hcolumn j v) : v.val < 2^34 := by
  dsimp [columnTotal, sumFour] at hv
  have h0 : (limbAt (state.val[column.val]'(by scalar_tac))
      (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt).val < 2^32 := by scalar_tac
  have h1 : (limbAt (state.val[4+column.val]'(by scalar_tac))
      (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt).val < 2^32 := by scalar_tac
  have h2 : (limbAt (state.val[8+column.val]'(by scalar_tac))
      (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt).val < 2^32 := by scalar_tac
  have h3 : (limbAt (state.val[12+column.val]'(by scalar_tac))
      (UScalar.ofNatCore j.val (by scalar_tac)) j.isLt).val < 2^32 := by scalar_tac
  omega

private def rowModel (state : State) (column : Usize) (hcolumn : column.val < 4)
    (row : Row) : Prop :=
  ∀ j : Fin 4, columnTotal state column hcolumn j (cell row j)

private def rowBound (state : State) (column : Usize) (hcolumn : column.val < 4)
    (row : Row) : Prop :=
  ∀ j : Fin 4, (cell row j).val < 2^34

/-- The actual four-column `array_from_fn_copy` used by external_linear_lazy
    succeeds. Each returned U64 limb is bounded from the four checked U32
    source operands, providing the addition safety condition for loop 1. -/
theorem source_success (state : State) :
    ∃ sums : Sums,
      array_from_fn_copy 4#usize
        (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
        state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
        (Array.repeat 4#usize 0#u64) state = .ok sums ∧
      (∀ i j : Fin 4, columnTotal state (UScalar.ofNatCore i.val (by scalar_tac))
        (by scalar_tac) j (cell (sums.val[i.val]'(by simpa [sums.property] using i.isLt)) j)) ∧
      ∀ i j : Fin 4, (sumWordAt sums i j).val < 2^34 := by
  let inst := state_only_poseidon.external_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
  have hcols : ∀ j : Fin 4, ∃ row : Row,
      inst.call_mut state (UScalar.ofNatCore j.val (by scalar_tac)) = .ok (row,state) ∧
      rowModel state (UScalar.ofNatCore j.val (by scalar_tac)) (by scalar_tac) row ∧
        rowBound state (UScalar.ofNatCore j.val (by scalar_tac)) (by scalar_tac) row := by
    intro j
    let column : Usize := UScalar.ofNatCore j.val (by scalar_tac)
    have hcolumn : column.val < 4 := by scalar_tac
    obtain ⟨row,hrun,hprops⟩ := external_column_array_call state column hcolumn
    refine ⟨row,hrun,?_,?_⟩
    · exact hprops
    · intro j
      exact column_output_bound state column hcolumn j (cell row j) (hprops j)
  choose rows hrows hmodels hbounded using hcols
  let value : Nat → Row := fun n => if h : n < 4 then rows ⟨n,h⟩ else Array.repeat 4#usize 0#u64
  have hstable : ∀ i : Usize, i.val < (4#usize).val →
      inst.call_mut state i = .ok (value i.val,state) := by
    intro i hi
    have hi4 : i.val < 4 := by simpa using hi
    let j : Fin 4 := ⟨i.val,hi4⟩
    have hj := hrows j
    have hindex : (UScalar.ofNatCore j.val (by scalar_tac) : Usize) = i := by
      apply UScalar.eq_of_val_eq
      scalar_tac
    have hcall : inst.call_mut state i = .ok (rows j,state) := by
      rw [← hindex]
      exact hj
    simpa only [value, dif_pos hi4] using hcall
  obtain ⟨sums,hrun,hsums⟩ := AspisR1SelectedMaskProbe.array_from_fn_copy_stable
    4#usize (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
    inst (Array.repeat 4#usize 0#u64) state value hstable
  refine ⟨sums,hrun,?_,?_⟩
  · intro i j
    have hi : i.val < (4#usize).val := by simpa using i.isLt
    have hread := hsums i.val hi
    have hbound : i.val < 4 := by simpa using i.isLt
    have hrow : sums.val[i.val]'(by simpa [sums.property] using i.isLt) = rows i := by
      simpa [value,hbound] using hread
    have hmodel := hmodels i j
    change columnTotal state (UScalar.ofNatCore i.val (by scalar_tac)) (by scalar_tac) j
      (cell (cell sums i) j)
    have hrowCell : cell sums i = rows i := by simpa [cell] using hrow
    rw [hrowCell]
    exact hmodel
  · intro i j
    have hi : i.val < (4#usize).val := by simpa using i.isLt
    have hread := hsums i.val hi
    have hbound : i.val < 4 := by simpa using i.isLt
    have hmodel : rowModel state (UScalar.ofNatCore i.val (by scalar_tac))
        (by scalar_tac) (rows i) := hmodels i
    have hrow : sums.val[i.val]'(by simpa [sums.property] using i.isLt) = rows i := by
      simpa [value,hbound] using hread
    have hrowBound := hbounded i j
    change (cell (cell sums i) j).val < 2^34
    have hrowCell : cell sums i = rows i := by simpa [cell] using hrow
    simpa [hrowCell] using hrowBound

#print axioms source_success
end AspisR1.PoseidonExternalColumnSums
