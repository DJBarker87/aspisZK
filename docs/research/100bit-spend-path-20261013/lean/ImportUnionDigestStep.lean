import AspisR1TerminalDigestBindingCandidate.Source
import AspisR1TerminalDigestBindingCandidate.Exact

/-! Symbolic lane-step normalization. The continuation is a parameter, so kernel
checking this straight-line composition cannot unfold the recursive loop. -/
set_option autoImplicit false
namespace ImportUnionDigestStep
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate
open AspisR1TerminalDigestBindingCandidate.Exact

abbrev Range := core.ops.range.Range Usize
abbrev Output := Array field.QM31 8#usize

def rawStep (nextLoop : Range → Output → Result Output) (iter1 : Range)
    (lane : Usize) (base : Output) (selector : field.QM31)
    (opened : Array field.QM31 16#usize) (start : Usize)
    (expected : Array field.M31 8#usize) (rightTweak : Bool) : Result Output := do
  let target ← Array.index_usize expected lane
  let (iter2, target1) ←
    if rightTweak then do
      let i ← lane + 1#usize
      let m ← if i = poseidon2.DIGEST_ELEMS then
        field.M31.add target poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK
        else Result.ok target
      Result.ok (iter1, m)
    else Result.ok (iter1, target)
  let q ← Array.index_usize base lane
  let i ← start + lane
  let q1 ← Array.index_usize opened i
  let q2 ← pool_v1.pair_forest_semantic_terminal.lift_m31 target1
  let q3 ← field.QM31.sub q1 q2
  let q4 ← field.QM31.mul selector q3
  let q5 ← field.QM31.add q q4
  let a ← Array.update base lane q5
  nextLoop iter2 a

def step (nextLoop : Range → Output → Result Output) (iter1 : Range)
    (lane : Usize) (base : Output) (selector : field.QM31)
    (opened : Array field.QM31 16#usize) (start : Usize)
    (expected : Array field.M31 8#usize) (rightTweak : Bool) : Result Output := do
  let target ← Array.index_usize expected lane
  let target1 ← targetAfterLane lane target rightTweak
  let q ← Array.index_usize base lane
  let i ← start + lane
  let q1 ← Array.index_usize opened i
  let q2 ← pool_v1.pair_forest_semantic_terminal.lift_m31 target1
  let q3 ← field.QM31.sub q1 q2
  let q4 ← field.QM31.mul selector q3
  let q5 ← field.QM31.add q q4
  let a ← Array.update base lane q5
  nextLoop iter1 a

theorem rawStep_eq_step (nextLoop : Range → Output → Result Output) (iter1 : Range)
    (lane : Usize) (base : Output) (selector : field.QM31)
    (opened : Array field.QM31 16#usize) (start : Usize)
    (expected : Array field.M31 8#usize) (rightTweak : Bool) :
    rawStep nextLoop iter1 lane base selector opened start expected rightTweak =
      step nextLoop iter1 lane base selector opened start expected rightTweak := by
  have uncurry_as_projections {α β γ : Type} (f : α → β → γ) :
      Aeneas.Std.uncurry f = fun p : α × β => f p.1 p.2 := by
    funext p
    rcases p with ⟨a, b⟩
    exact Aeneas.Std.uncurry_apply_pair f a b
  cases rightTweak <;>
    simp only [rawStep, step, targetAfterLane, Bool.false_eq_true, ite_false,
      ite_true, bind_tc_ok, bind_assoc_eq, uncurry_as_projections]

theorem step_success (nextLoop : Range → Output → Result Output) (iter1 : Range)
    (lane : Usize) (base : Output) (selector : field.QM31)
    (opened : Array field.QM31 16#usize) (start : Usize)
    (expected : Array field.M31 8#usize) (rightTweak : Bool)
    (expectedLane target : field.M31) (old openedLane lifted difference scaled updated : field.QM31)
    (openedIndex : Usize) (out final : Output)
    (hexpected : Array.index_usize expected lane = Result.ok expectedLane)
    (htarget : targetAfterLane lane expectedLane rightTweak = Result.ok target)
    (hbase : Array.index_usize base lane = Result.ok old)
    (hoffset : (start + lane : Result Usize) = Result.ok openedIndex)
    (hopened : Array.index_usize opened openedIndex = Result.ok openedLane)
    (hlift : pool_v1.pair_forest_semantic_terminal.lift_m31 target = Result.ok lifted)
    (hsub : field.QM31.sub openedLane lifted = Result.ok difference)
    (hmul : field.QM31.mul selector difference = Result.ok scaled)
    (hadd : field.QM31.add old scaled = Result.ok updated)
    (hupdate : Array.update base lane updated = Result.ok out)
    (hcontinue : nextLoop iter1 out = Result.ok final) :
    step nextLoop iter1 lane base selector opened start expected rightTweak = Result.ok final := by
  simp only [step, hexpected, htarget, hbase, hoffset, hopened, hlift, hsub,
    hmul, hadd, hupdate, hcontinue, bind_tc_ok]

#print axioms rawStep_eq_step
#print axioms step_success
end ImportUnionDigestStep
