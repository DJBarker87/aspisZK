import PoseidonExternalLazySourceCut
import AspisR1.PoseidonExternalLoopCanonical
import PoseidonExternalColumnSumsV4
import PoseidonExternalColumnSumFieldV4
import PoseidonExternalLoop1Fuel
import PoseidonExternalColumn1Reassembly
import AspisR1.PoseidonGroupSliceModel
import AspisR1.PoseidonFullRoundCellStep

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalLinearExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonGroupSliceModel
open AspisR1.PoseidonFullRoundCellStep

abbrev State := Array field.QM31 16#usize
abbrev Sums := Array (Array Std.U64 4#usize) 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev CanonicalState := AspisR1.PoseidonFullRoundCellStep.CanonicalState
abbrev Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact

private theorem cell16_eq_cellAt (a : State) (g j : Fin 4) :
    cell16 a g j = AspisR1.PoseidonExternalGroupUpdateCells.cellAt a (4*g.val+j.val) := by
  have h16 : (16#usize).val = 16 := by scalar_tac
  have hidx : 4*g.val+j.val < 16 := by have := g.isLt; have := j.isLt; omega
  simp [cell16, AspisR1.PoseidonExternalGroupUpdateCells.cellAt, hidx]

private theorem cell16_eq_cell (a : State) (g j : Fin 4) :
    cell16 a g j = cell a ⟨4*g.val+j.val, by
      have h16 : (16#usize).val = 16 := by scalar_tac
      have := g.isLt; have := j.isLt; omega⟩ := by
  simp [cell16, cell]

private theorem field_column_model (input stage : State) (column : Fin 4)
    (hmat : ∀ g j : Fin 4,
      Decode (cell16 stage g j) =
        R0P.poseidonMat4 (fun k => Decode (cell16 input g k)) j) :
    AspisR1.PoseidonExternalColumnSumField.fieldColumnSum stage column =
      (((0 + R0P.poseidonMat4 (fun k => Decode (cell16 input 0 k)) column) +
        R0P.poseidonMat4 (fun k => Decode (cell16 input 1 k)) column) +
        R0P.poseidonMat4 (fun k => Decode (cell16 input 2 k)) column) +
        R0P.poseidonMat4 (fun k => Decode (cell16 input 3 k)) column := by
  simp only [AspisR1.PoseidonExternalColumnSumField.fieldColumnSum,
    AspisR1.PoseidonExternalColumnSumField.rowWordsAt,
    AspisR1.PoseidonExternalColumn1Reassembly.qWords_decode]
  have hm (g : Fin 4) : AspisR1.PoseidonExternalColumn1Reassembly.Decode
      (cell16 stage g column) =
      R0P.poseidonMat4 (fun k => Decode (cell16 input g k)) column := by
    simpa [AspisR1.PoseidonExternalColumn1Reassembly.Decode, Decode] using hmat g column
  rw [hm 0, hm 1, hm 2, hm 3]
  simp only [zero_add]

private def decodeState (s : State) : Fin 16 → Exact := fun i => Decode (cell s i)

private theorem input_group_cell (input : State) (g j : Fin 4) :
    Decode (cell16 input g j) = decodeState input ⟨4*g.val+j.val, by
      have := g.isLt; have := j.isLt; omega⟩ := by
  change Decode (cell input (⟨4*g.val+j.val, by
    have h16 : (16#usize).val = 16 := by scalar_tac
    have := g.isLt; have := j.isLt; omega⟩ : Fin 16)) =
      Decode (cell input ⟨4*g.val+j.val, by
        have h16 : (16#usize).val = 16 := by scalar_tac
        have := g.isLt; have := j.isLt; omega⟩)
  rfl

theorem external_linear_lazy_success (input : State)
    (hinput : CanonicalState input) :
    ∃ out : State,
      state_only_poseidon.external_linear_lazy input = .ok out ∧
      CanonicalState out ∧
      ∀ i : Fin 16, Decode (cell out i) =
        R0P.poseidonExternalLinear (decodeState input) i := by
  obtain ⟨stage,hloop0,hgroupModel⟩ :=
    AspisR1.PoseidonExternalLoopFuel.loop0_all_groups input
  obtain ⟨stageCan,hloop0Can,hstageCan⟩ :=
    AspisR1.PoseidonExternalLoopCanonical.loop0_success_canonical_fuel
      input 0#usize 4 (by decide) hinput
  have hstageEq : stageCan = stage := Result.ok.inj (hloop0Can.symm.trans hloop0)
  subst stageCan
  obtain ⟨sums,hsumsRun,hcolumns,hsumsBound⟩ :=
    AspisR1.PoseidonExternalColumnSums.source_success stage
  have hcolumns' : ∀ i j : Fin 4,
      AspisR1.PoseidonExternalColumnArrayCall.columnTotal stage
        (UScalar.ofNatCore i.val (by scalar_tac)) (by scalar_tac) j
        (AspisR1.PoseidonExternalColumnSums.sumWordAt sums i j) := by
    intro i j
    simpa [AspisR1.PoseidonExternalColumnSums.sumWordAt,
      AspisR1.PoseidonFullRoundCellStep.cell] using hcolumns i j
  have hcolumnModel (column : Fin 4) :=
    AspisR1.PoseidonExternalColumnSumField.source_column_decode
      stage sums hcolumns' column
  have hsumBound : ∀ i j : Fin 4,
      (AspisR1.PoseidonExternalColumn1Call.sumWordAt sums i j).val < 2^34 := by
    intro i j
    simpa [AspisR1.PoseidonExternalColumn1Call.sumWordAt,
      AspisR1.PoseidonExternalColumnSums.sumWordAt,
      AspisR1.PoseidonFullRoundCellStep.cell] using hsumsBound i j
  have hinvariant : AspisR1.PoseidonExternalLoop1Fuel.loopModel stage stage sums 0 := by
    intro i
    simp [AspisR1.PoseidonExternalLoop1Fuel.loopModel]
  obtain ⟨out,hloop1,houtCan,hloop1Model⟩ :=
    AspisR1.PoseidonExternalLoop1Fuel.loop1_success_fuel
      stage stage sums 0#usize 16 (by decide) hinvariant hstageCan hsumBound
  have hsource : state_only_poseidon.external_linear_lazy input = .ok out := by
    simp [state_only_poseidon.external_linear_lazy,hloop0,hsumsRun,bind_tc_ok,hloop1]
  have hmat : ∀ g j : Fin 4,
      Decode (cell16 stage g j) =
        R0P.poseidonMat4 (fun k => Decode (cell16 input g k)) j := by
    intro g j
    have h := hgroupModel g j
    rw [← cell16_eq_cellAt stage g j] at h
    exact h
  refine ⟨out,hsource,houtCan,?_⟩
  intro i
  have hvalue := hloop1Model i
  simp only [AspisR1.PoseidonExternalLoop1Fuel.loopModel, if_pos i.isLt] at hvalue
  let group : Fin 4 := ⟨i.val / 4, by omega⟩
  let column : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩
  have hindex : (⟨4*group.val+column.val, by
      have := group.isLt; have := column.isLt; omega⟩ : Fin 16) = i := by
    apply Fin.ext
    simp [group,column]
    omega
  have hlocal : Decode (cell stage i) =
      R0P.poseidonMat4 (fun k => Decode (cell16 input group k)) column := by
    have hm := hmat group column
    have hcell : cell16 stage group column = cell stage i := by
      rw [← hindex]
      exact cell16_eq_cell stage group column
    rw [hcell] at hm
    exact hm
  have hinc : AspisR1.PoseidonExternalLoop1Fuel.incrementAt sums i =
      AspisR1.PoseidonExternalColumnSumField.fieldColumnSum stage column := by
    dsimp [AspisR1.PoseidonExternalLoop1Fuel.incrementAt]
    have hcol := hcolumnModel column
    have hfin : (⟨i.val % 4, Nat.mod_lt _ (by omega)⟩ : Fin 4) = column := by
      apply Fin.ext
      simp [column]
    rw [hfin]
    exact hcol
  have hfield := field_column_model input stage column hmat
  have hmodelRhs : Decode (cell stage i) +
      AspisR1.PoseidonExternalLoop1Fuel.incrementAt sums i =
      R0P.poseidonExternalLinear (decodeState input) i := by
    rw [hlocal,hinc,hfield]
    simp [R0P.poseidonExternalLinear,decodeState,group,column,input_group_cell]
  exact hvalue.trans hmodelRhs

#print axioms external_linear_lazy_success
end AspisR1.PoseidonExternalLinearExact
