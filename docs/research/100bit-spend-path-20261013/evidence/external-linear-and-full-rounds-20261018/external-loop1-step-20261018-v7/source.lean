import PoseidonExternalLoop1Source
import PoseidonExternalColumn1ArrayCall
import PoseidonInternalStateWords
import AspisR1.PoseidonFullRoundCellStep
import Aeneas.Std.WP

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalLoop1Step
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLoop1Source
open AspisR1.PoseidonExternalColumn1Reassembly (sumWords)
open AspisR1.PoseidonFullRoundCellStep

abbrev State := Array field.QM31 16#usize
abbrev QM := field.QM31
abbrev Sums := Array (Array Std.U64 4#usize) 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact

def laneIncrement (sums : Sums) (lane : Usize) : Exact :=
  AspisR1.RawPoseidonRowField.decodeWords
    (sumWords sums ⟨lane.val % 4, Nat.mod_lt _ (by omega)⟩)

theorem loop1_step_success (state : State) (sums : Sums) (lane : Usize)
    (hlane : lane.val < 16) (hstate : CanonicalState state)
    (hsums : ∀ i j : Fin 4,
      (AspisR1.PoseidonExternalColumn1Call.sumWordAt sums i j).val < 2^34) :
    ∃ value nextLane,
      AspisR1.PoseidonExternalLoop1Source.runStep state sums lane = .ok (state.set lane value,nextLane) ∧
      nextLane.val = lane.val + 1 ∧
      Canonical value ∧
      CanonicalState (state.set lane value) ∧
      Decode value = Decode (cell state ⟨lane.val,hlane⟩) + laneIncrement sums lane ∧
      ∀ j : Fin 16,
        Decode (cell (state.set lane value) j) =
          if j.val = lane.val then Decode (cell state ⟨lane.val,hlane⟩) + laneIncrement sums lane
          else Decode (cell state j) := by
  let index : Fin 16 := ⟨lane.val,hlane⟩
  let q := cell state index
  have hread : Array.index_usize state lane = .ok q := by
    simpa only [q,index] using
      AspisR1.PoseidonInternalStateWords.state_source_read state lane hlane
  obtain ⟨raw,value,harray,hcanonical,hmodel⟩ :=
    AspisR1.PoseidonExternalColumn1ArrayCall.source_success q sums lane hlane hsums
  have hupdate : Array.update state lane value = .ok (state.set lane value) := by
    obtain ⟨out,hrun,hset⟩ := WP.spec_imp_exists
      (Array.update_spec state lane value (by simpa [state.property] using hlane))
    simpa only [hset] using hrun
  have hincSpec : (lane + 1#usize : Result Usize) ⦃z => z.val = lane.val + 1⦄ := by
    apply UScalar.add_spec
    scalar_tac
  obtain ⟨nextLane,hinc,hincVal⟩ := WP.spec_imp_exists hincSpec
  have hq : q = cell state ⟨lane.val,hlane⟩ := by rfl
  have hmodel' : Decode value = Decode q + laneIncrement sums lane := by
    change Decode value = Decode q + laneIncrement sums lane at hmodel
    exact hmodel
  let pairAction : Result (Array U64 4#usize × QM) := do
    let limbs ← state_only_poseidon.extension_limbs q
    let raw ← array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (limbs,sums,lane)
    let out ← state_only_poseidon.extension_from_raw_limbs raw
    ok (raw,out)
  have hpair : pairAction = .ok (raw,value) := by simpa [pairAction] using harray
  have hcontinued : (do
      let pair ← pairAction
      let state1 ← Array.update state lane pair.2
      ok (state1,nextLane)) = .ok (state.set lane value,nextLane) := by
    simp only [hpair, hupdate, bind_tc_ok]
  have hflatten : (do
      let limbs ← state_only_poseidon.extension_limbs q
      let raw ← array_from_fn_copy 4#usize core.marker.CopyU64
        state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        0#u64 (limbs,sums,lane)
      let value1 ← state_only_poseidon.extension_from_raw_limbs raw
      let state1 ← Array.update state lane value1
      ok (state1,nextLane)) = (do
      let pair ← pairAction
      let state1 ← Array.update state lane pair.2
      ok (state1,nextLane)) := by
    simp [pairAction, bind_assoc_eq]
  refine ⟨value,nextLane,?_,hincVal,hcanonical,
    set_canonical state lane value hstate hcanonical,?_ ,?_⟩
  · rw [AspisR1.PoseidonExternalLoop1Source.runStep, hread, bind_tc_ok, hinc]
    simpa only [hflatten, bind_tc_ok] using hcontinued
  · change Decode value = Decode q + laneIncrement sums lane
    exact hmodel'
  · intro j
    rw [cell_set]
    by_cases heq : j.val = lane.val
    · have hj : j = index := Fin.ext heq
      subst j
      rw [hq] at hmodel'
      simpa [index] using hmodel'
    · simp [heq]

#print axioms loop1_step_success
end AspisR1.PoseidonExternalLoop1Step
