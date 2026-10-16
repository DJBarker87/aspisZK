import PathLaneSourceStep
import OccupancyRangeTraversal

/-! Symbolic source-loop induction for the eight paired path updates.
The finite state model avoids reducing concrete field recurrences. -/
set_option autoImplicit false
namespace AspisR1.PathLaneSourceLoop
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PathLaneSourceStep
open AspisR1.PreweightedGroupUpdate
open AspisR1.ExtractedMaskQM31Exact

abbrev State := Fin 17 → ExactQM
abbrev Range := core.ops.range.Range Usize
abbrev Loop := AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop

def read16 (a : Array QM 16#usize) (i : Nat) : ExactQM :=
  if h : i < 16 then decode (cell a ⟨i, by simpa using h⟩) else 0

def decoded (path : Array QM 17#usize) : State := fun j => decode (cell path j)

def left (selector bit : QM) (a a1 : Array QM 16#usize) (lane : Nat) : ExactQM :=
  decode selector * (1 - decode bit) * (read16 a1 lane - read16 a (1 + lane))

def right (selector bit : QM) (a a1 : Array QM 16#usize) (lane : Nat) : ExactQM :=
  decode selector * decode bit * (read16 a1 (8 + lane) - read16 a (1 + lane))

def step (selector bit : QM) (a a1 : Array QM 16#usize) (lane : Nat) (s : State) : State :=
  fun j => if j.val = 1 + lane then left selector bit a a1 lane
    else if j.val = 9 + lane then right selector bit a a1 lane else s j

def applySteps (selector bit : QM) (a a1 : Array QM 16#usize) : Nat → Nat → State → State
  | 0, _, s => s
  | n + 1, lane, s => applySteps selector bit a a1 n (lane + 1)
      (step selector bit a a1 lane s)

theorem runStep_model
    (lane : Usize) (selector : QM) (a a1 : Array QM 16#usize)
    (bit : QM) (path : Array QM 17#usize)
    (hlane : lane.val < 8) (hs : Canonical selector) (hb : Canonical bit)
    (ha : CanonicalArray a) (ha1 : CanonicalArray a1) (hp : CanonicalArray path) :
    ∃ out, runStep lane selector a a1 bit path = .ok out ∧ CanonicalArray out ∧
      decoded out = step selector bit a a1 lane.val (decoded path) := by
  obtain ⟨out, hrun, hcanonical, hvalues⟩ :=
    runStep_success lane selector a a1 bit path hlane hs hb ha ha1 hp
  refine ⟨out, hrun, hcanonical, ?_⟩
  funext j
  have h0 : lane.val < 16 := by omega
  have h1 : 1 + lane.val < 16 := by omega
  have h8 : 8 + lane.val < 16 := by omega
  simpa only [decoded, step, left, right, read16, dif_pos h0, dif_pos h1, dif_pos h8]
    using hvalues j

theorem loop_model
    (fuel : Nat) (iter : Range) (selector : QM) (a a1 : Array QM 16#usize)
    (bit : QM) (path : Array QM 17#usize)
    (hend : iter.end.val = 8) (hspan : iter.start.val + fuel = 8)
    (hs : Canonical selector) (hb : Canonical bit)
    (ha : CanonicalArray a) (ha1 : CanonicalArray a1) (hp : CanonicalArray path) :
    ∃ out, Loop iter selector a a1 bit path = .ok out ∧ CanonicalArray out ∧
      decoded out = applySteps selector bit a a1 fuel iter.start.val (decoded path) := by
  induction fuel generalizing iter path with
  | zero =>
      have hdone : iter.start.val ≥ iter.end.val := by omega
      refine ⟨path, ?_, hp, rfl⟩
      change AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop
        iter selector a a1 bit path = .ok path
      rw [AspisR1.PathLaneSourceStep.generated_loop_step, AspisR1.OccupancyRangeTraversal.next_done iter hdone]
      simp only [bind_tc_ok]
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hlane : iter.start.val < 8 := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _hbound⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      obtain ⟨path1, hstep, hcanonical1, hmodel1⟩ :=
        runStep_model iter.start selector a a1 bit path hlane hs hb ha ha1 hp
      obtain ⟨out, hrun, hcanonical, hmodel⟩ :=
        ih iter1 path1 (by simpa only [hend1] using hend) (by omega) hcanonical1
      refine ⟨out, ?_, hcanonical, ?_⟩
      · change AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal_loop
          iter selector a a1 bit path = .ok out
        rw [AspisR1.PathLaneSourceStep.generated_loop_step]
        simp only [hnext, bind_tc_ok, hstep, hrun]
      · rw [hmodel, hstart1, hmodel1]
        rfl

#print axioms runStep_model
#print axioms loop_model
end
end AspisR1.PathLaneSourceLoop
