import PoseidonFullRoundLoopModel

/-! Actual leading absorption: a fixed input array is added to distinct
state cells over the checked source range. The invariant is symbolic. -/
set_option autoImplicit false
namespace AspisR1.PoseidonLeadingAbsorb
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
abbrev Range := core.ops.range.Range Usize

def addStep (a state : State) (lane : Usize) : Result State := do
  let x ← Array.index_usize state lane
  let y ← Array.index_usize a lane
  let value ← field.QM31.add x y
  Array.update state lane value

def addModel (a state : State) (lane : Fin 16) : Exact :=
  Decode (cell state lane) + Decode (cell a lane)

theorem addStep_success (a state : State) (lane : Usize) (hlane : lane.val < 16)
    (ha : CanonicalState a) (hs : CanonicalState state) :
    ∃ value : QM, addStep a state lane = .ok (state.set lane value) ∧
      CanonicalState (state.set lane value) ∧
      ∀ j : Fin 16, Decode (cell (state.set lane value) j) =
        if j.val = lane.val then addModel a state ⟨lane.val,hlane⟩ else Decode (cell state j) := by
  let index : Fin 16 := ⟨lane.val,hlane⟩
  let x := cell state index
  let y := cell a index
  have hb : lane.val < (16#usize).val := by simpa using hlane
  have hx : Array.index_usize state lane = .ok x := by
    simpa only [x,index,cell] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok state lane hb
  have hy : Array.index_usize a lane = .ok y := by
    simpa only [y,index,cell] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok a lane hb
  obtain ⟨value,hadd,hcan,hmodel⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact x y (hs index) (ha index)
  obtain ⟨out,hupdate,hset⟩ := WP.spec_imp_exists (Array.update_spec state lane value (by simpa [state.property] using hb))
  have hwrite : Array.update state lane value = .ok (state.set lane value) := by
    rw [hupdate,hset]
  refine ⟨value,?_,set_canonical state lane value hs hcan,?_⟩
  · simp only [addStep,hx,hy,bind_tc_ok,hadd,hwrite]
  · intro j
    rw [cell_set]
    by_cases hj : j.val = lane.val
    · simp only [if_pos hj]
      exact hmodel
    · simp only [if_neg hj]

theorem generated_loop_step (iter : Range) (a state : State) :
    state_only_poseidon.leading_pair_packed_loop iter a state = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok state
      | some lane =>
        let state1 ← addStep a state lane
        state_only_poseidon.leading_pair_packed_loop iter1 a state1) := by
  rw [state_only_poseidon.leading_pair_packed_loop.eq_def]
  simp only [addStep,bind_assoc_eq]
  rfl

theorem loop_success_fuel (a state : State) (iter : Range) (fuel : Nat)
    (hend : iter.end.val ≤ 16) (hspan : iter.start.val + fuel = iter.end.val)
    (ha : CanonicalState a) (hs : CanonicalState state) :
    ∃ out : State, state_only_poseidon.leading_pair_packed_loop iter a state = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) =
        if iter.start.val ≤ j.val ∧ j.val < iter.end.val then addModel a state j
        else Decode (cell state j) := by
  induction fuel generalizing state iter with
  | zero =>
    have hstop : iter.start.val ≥ iter.end.val := by omega
    have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
    refine ⟨state,?_,hs,?_⟩
    · rw [generated_loop_step,hnext]
      change Result.ok state = Result.ok state
      rfl
    · intro j
      have hn : ¬ (iter.start.val ≤ j.val ∧ j.val < iter.end.val) := by omega
      rw [if_neg hn]
  | succ fuel ih =>
    have hlt : iter.start.val < iter.end.val := by omega
    have hidx : iter.start.val < 16 := by omega
    obtain ⟨iter1,hnext,hinc,hend1,_⟩ := AspisR1.OccupancyRangeTraversal.next_step iter hlt
    have hend' : iter1.end.val ≤ 16 := by rw [hend1]; exact hend
    have hspan' : iter1.start.val + fuel = iter1.end.val := by rw [hend1]; omega
    obtain ⟨value,hstep,hstate1,hcells⟩ := addStep_success a state iter.start hidx ha hs
    let state1 := state.set iter.start value
    obtain ⟨out,hrec,hcan,hmodel⟩ := ih state1 iter1 hend' hspan' hstate1
    refine ⟨out,?_,hcan,?_⟩
    · rw [generated_loop_step,hnext]
      change (do
        let nextState ← addStep a state iter.start
        state_only_poseidon.leading_pair_packed_loop iter1 a nextState) = .ok out
      rw [hstep]
      change state_only_poseidon.leading_pair_packed_loop iter1 a state1 = .ok out
      exact hrec
    · intro j
      have hv := hmodel j
      rw [hinc,hend1] at hv
      rw [hv]
      by_cases hj : j.val = iter.start.val
      · have hafter : ¬ (iter.start.val + 1 ≤ j.val ∧ j.val < iter.end.val) := by omega
        have hinside : iter.start.val ≤ j.val ∧ j.val < iter.end.val := by omega
        rw [if_neg hafter,if_pos hinside]
        have hcell := hcells j
        rw [if_pos hj] at hcell
        have hindex : (⟨iter.start.val,hidx⟩ : Fin 16) = j := Fin.ext hj.symm
        change Decode (cell state1 j) = addModel a state ⟨iter.start.val,hidx⟩ at hcell
        exact hcell.trans (congrArg (addModel a state) hindex)
      · have hcell : Decode (cell state1 j) = Decode (cell state j) := by
          have h := hcells j
          rw [if_neg hj] at h
          exact h
        unfold addModel
        rw [hcell]
        have hrange : (iter.start.val + 1 ≤ j.val ∧ j.val < iter.end.val) ↔
            (iter.start.val ≤ j.val ∧ j.val < iter.end.val) := by omega
        by_cases hin : iter.start.val ≤ j.val ∧ j.val < iter.end.val
        · rw [if_pos (hrange.mpr hin),if_pos hin]
        · have hn : ¬ (iter.start.val + 1 ≤ j.val ∧ j.val < iter.end.val) :=
            fun h => hin (hrange.mp h)
          rw [if_neg hn,if_neg hin]

theorem source_success (a state : State) (ha : CanonicalState a) (hs : CanonicalState state) :
    ∃ out : State,
      state_only_poseidon.leading_pair_packed_loop
        { start := 0#usize, «end» := poseidon2.RATE } a state = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) =
        if j.val < 8 then addModel a state j else Decode (cell state j) := by
  have hrate : poseidon2.RATE = 8#usize := by unfold poseidon2.RATE; rfl
  obtain ⟨out,hrun,hcan,hmodel⟩ := loop_success_fuel a state
    { start := 0#usize, «end» := 8#usize } 8 (by decide) (by decide) ha hs
  refine ⟨out,?_,hcan,?_⟩
  · rw [hrate]
    exact hrun
  · intro j
    have h := hmodel j
    have hzero : (0#usize).val ≤ j.val := Nat.zero_le _
    have height : (8#usize).val = 8 := by decide
    simpa only [hzero,true_and,height] using h

#print axioms addStep_success
#print axioms generated_loop_step
#print axioms loop_success_fuel
#print axioms source_success
end AspisR1.PoseidonLeadingAbsorb
