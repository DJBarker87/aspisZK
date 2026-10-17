import PoseidonQMFullRoundSource
import AspisR1.PoseidonFullRoundCellStep

set_option autoImplicit false
namespace AspisR1.PoseidonQMFullRoundCellStep
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep

def runStep (state constants1 : State) (lane : Usize) : Result State := do
  let x ← Array.index_usize state lane
  let y ← Array.index_usize constants1 lane
  let added ← field.QM31.add x y
  let value ← state_only_poseidon.pow5 added
  Array.update state lane value

theorem runStep_success (state constants1 : State) (lane : Usize) (hlane : lane.val < 16)
    (hstate : CanonicalState state) (hconstants : CanonicalState constants1) :
    ∃ value : QM, runStep state constants1 lane = .ok (state.set lane value) ∧
      Canonical value ∧ CanonicalState (state.set lane value) ∧
      Decode value = R0P.poseidonPow5
        (Decode (cell state ⟨lane.val,hlane⟩) + Decode (cell constants1 ⟨lane.val,hlane⟩)) ∧
      ∀ j : Fin 16, Decode (cell (state.set lane value) j) =
        if j.val = lane.val then R0P.poseidonPow5
          (Decode (cell state ⟨lane.val,hlane⟩) + Decode (cell constants1 ⟨lane.val,hlane⟩))
        else Decode (cell state j) := by
  let index : Fin 16 := ⟨lane.val,hlane⟩
  let x := cell state index
  let y := cell constants1 index
  have hb : lane.val < (16#usize).val := by simpa using hlane
  have hx : Array.index_usize state lane = .ok x := by
    simpa only [x,index,cell] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok state lane hb
  have hy : Array.index_usize constants1 lane = .ok y := by
    simpa only [y,index,cell] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok constants1 lane hb
  obtain ⟨added,hadd,haddedCan,haddedModel⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact x y (hstate index) (hconstants index)
  obtain ⟨value,hpow,hcan,hmodel⟩ := AspisR1.PoseidonPow5SourceExact.source_success added haddedCan
  change Decode added = Decode x + Decode y at haddedModel
  change Decode value = R0P.poseidonPow5 (Decode added) at hmodel
  have hvalue : Decode value = R0P.poseidonPow5 (Decode x + Decode y) :=
    hmodel.trans (congrArg R0P.poseidonPow5 haddedModel)
  obtain ⟨out,hupdate,hset⟩ := WP.spec_imp_exists
    (Array.update_spec state lane value (by simpa [state.property] using hb))
  have hwrite : Array.update state lane value = .ok (state.set lane value) := by rw [hupdate,hset]
  refine ⟨value,?_,hcan,set_canonical state lane value hstate hcan,hvalue,?_⟩
  · simp only [runStep,hx,hy,bind_tc_ok,hadd,hpow,hwrite]
  · intro j
    rw [cell_set]
    by_cases hj : j.val = lane.val
    · simp only [if_pos hj]
      exact hvalue
    · simp only [if_neg hj]

#print axioms runStep_success
end AspisR1.PoseidonQMFullRoundCellStep
