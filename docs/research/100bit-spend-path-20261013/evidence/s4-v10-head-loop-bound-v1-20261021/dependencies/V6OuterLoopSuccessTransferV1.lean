import V6OuterBatchBoundBridgeV1
import LoopSuccessTransferV1
import FourDotsBatchBodyAdvanceV1
import Aeneas.Std.RangeIter
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsV6OuterLoopSuccessTransferV1
abbrev Ops := AspisR1FastDotsActualBatchLimbBoundV1.Ops
abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsActualBatchLimbBoundV1.Wide
abbrev StepBy := AspisR1FastDotsActualBatchLimbBoundV1.StepBy
abbrev NewBody := AspisR1FastDotsV6OuterBatchBoundBridgeV1.NewBody
abbrev NewLoop := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0
abbrev OldBody := AspisR1FastDotsV6OuterBatchBoundBridgeV1.OldBody
abbrev OldLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
abbrev NewOps (ops : Ops) := AspisR1FastDotsActualBatchLimbBoundV1.BatchTermsOps
  (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops)
abbrev OldOps (ops : Ops) := AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps (NewOps ops)

def validState (s : StepBy × Array U64 8#usize) : Prop :=
  s.1.iter.end.val = 26 ∧ s.1.step_by = 4#usize

def newStep (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (s : StepBy × Array U64 8#usize) :=
  NewBody (NewOps ops) q g slot s.1 s.2

def oldStep (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (s : StepBy × Array U64 8#usize) :=
  OldBody (OldOps ops) q g slot s.1 s.2

def measure (s : StepBy × Array U64 8#usize) : Nat := s.1.iter.end.val - s.1.iter.start.val

theorem v6_outer_loop_success_old_loop
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs out : Array U64 8#usize)
    (hend : iter.iter.end.val = 26) (hstep : iter.step_by = 4#usize)
    (hnew : NewLoop (NewOps ops) iter q g slot limbs = .ok out) :
    OldLoop (OldOps ops) iter q g slot limbs = .ok out := by
  change Aeneas.Std.loop (newStep ops q g slot) (iter, limbs) = .ok out at hnew
  change Aeneas.Std.loop (oldStep ops q g slot) (iter, limbs) = .ok out
  apply AspisR1FastDotsLoopSuccessTransferV1.loop_success_transfer_invariant
    (newStep ops q g slot) (oldStep ops q g slot) measure validState
  · intro s flow hs
    rcases s with ⟨it, ls⟩
    exact AspisR1FastDotsV6OuterBatchBoundBridgeV1.new_body_success_old_body
      ops q g slot it ls flow rfl hs
  · intro s s' hinv hs
    rcases s with ⟨it, ls⟩
    rcases s' with ⟨it', ls'⟩
    rcases hinv with ⟨hend0, hstep0⟩
    have hold := AspisR1FastDotsV6OuterBatchBoundBridgeV1.new_body_success_old_body
      ops q g slot it ls (.cont (it', ls')) rfl hs
    obtain ⟨_, _, _, _, hend1, hstep1⟩ :=
      AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
        (OldOps ops) q g slot it it' ls ls' hstep0 hold
    exact ⟨by rw [hend1]; exact hend0, by rw [hstep1]; exact hstep0⟩
  · intro s s' hinv hs
    rcases s with ⟨it, ls⟩
    rcases s' with ⟨it', ls'⟩
    rcases hinv with ⟨hend0, hstep0⟩
    have hold := AspisR1FastDotsV6OuterBatchBoundBridgeV1.new_body_success_old_body
      ops q g slot it ls (.cont (it', ls')) rfl hs
    obtain ⟨_, hnext, _, hcursor, hend1, hstep1⟩ :=
      AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
        (OldOps ops) q g slot it it' ls ls' hstep0 hold
    have hpositive : it.step_by.val > 0 := by rw [hstep0]; simp
    have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec it hpositive
    rw [hnext, WP.spec_ok] at hspec
    have hstartlt : it.iter.start.val < it.iter.end.val := by
      by_contra hnot
      simp only [hnot, ↓reduceIte] at hspec
      rcases hspec with ⟨⟨hnone, _⟩, _, _⟩
      cases hnone
    have hdec : it'.iter.end.val - it'.iter.start.val < measure (it, ls) := by
      change it'.iter.end.val - it'.iter.start.val <
        it.iter.end.val - it.iter.start.val
      rw [hend1, hcursor]
      by_cases hmin : it.iter.start.val + it.step_by.val ≤ it.iter.end.val
      · rw [Nat.min_eq_left hmin]
        omega
      · have hlt : it.iter.end.val < it.iter.start.val + it.step_by.val :=
          Nat.lt_of_not_ge hmin
        have hle : it.iter.end.val ≤ it.iter.start.val + it.step_by.val := Nat.le_of_lt hlt
        rw [Nat.min_eq_right hle]
        omega
    exact hdec
  · exact ⟨hend, hstep⟩
  · exact hnew

#print axioms v6_outer_loop_success_old_loop
end AspisR1FastDotsV6OuterLoopSuccessTransferV1
