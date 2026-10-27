import R1Z.ProverCommitFourSteps
import R1Z.ProverCommitStreamBytes

/-! Universal oracle-support theorem for the extracted scalar/tower reference.
Only expander frames can affect its result. This does not identify the outer
material producer, its read order, or tree/binding/seed/salt coverage. -/
set_option autoImplicit false
namespace R1Z.ProverCommitReferenceReads
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R1Z.ProverCommitStepLoop (State Hash transition)
open R1Z.ProverCommitStreamSource (blockSlices Bytes32)

theorem next_support (left right : Hash) (domain : Slice U8) (state : State)
    (same : left (blockSlices domain state.seed state.counter) =
      right (blockSlices domain state.seed state.counter)) :
    prover_commit_reference.next left domain state =
      prover_commit_reference.next right domain state := by
  unfold blockSlices at same
  simp only [prover_commit_reference.next, lift]
  by_cases h : state.word = 8#usize
  · simp only [h, if_true, bind_tc_ok, same]
  · simp only [h, if_false]

theorem transition_support (left right : Hash) (domain : Slice U8)
    (same : ∀ (seed : Bytes32) (counter : U64),
      left (blockSlices domain seed counter) = right (blockSlices domain seed counter))
    (s : R1Z.ProverCommitStepLoop.Sample × State) :
    transition left domain s = transition right domain s := by
  rcases s with ⟨sample, state⟩
  cases sample with
  | Ok value => rfl
  | Err error =>
    simp only [transition, prover_commit_reference.try_step,
      next_support left right domain state (same state.seed state.counter)]

theorem scalar_support (left right : Hash) (domain : Slice U8)
    (same : ∀ (seed : Bytes32) (counter : U64),
      left (blockSlices domain seed counter) = right (blockSlices domain seed counter))
    (state : State) :
    prover_commit_reference.limb_caller left domain state =
      prover_commit_reference.limb_caller right domain state := by
  rw [R1Z.ProverCommitStepLoop.caller_step_induction,
    R1Z.ProverCommitStepLoop.caller_step_induction]
  exact R1Z.ProverCommitExtractedStep.iterate_refines _ _
    (transition_support left right domain same) 16 _

theorem all_calls_support (left right : Hash) (domain : Slice U8)
    (same : ∀ (seed : Bytes32) (counter : U64),
      left (blockSlices domain seed counter) = right (blockSlices domain seed counter))
    (n : Nat) (state : State) :
    R1Z.ProverCommitFourSteps.collect (prover_commit_reference.limb_caller left domain) n state =
    R1Z.ProverCommitFourSteps.collect (prover_commit_reference.limb_caller right domain) n state := by
  exact R1Z.ProverCommitFourSteps.collect_congr _ _
    (scalar_support left right domain same) n state

theorem tower_support (left right : Hash) (domain : Slice U8)
    (same : ∀ (seed : Bytes32) (counter : U64),
      left (blockSlices domain seed counter) = right (blockSlices domain seed counter))
    (state : State) :
    prover_commit_reference.qm31_caller left domain state =
      prover_commit_reference.qm31_caller right domain state := by
  simp only [prover_commit_reference.qm31_caller,
    scalar_support left right domain same]

#print axioms next_support
#print axioms transition_support
#print axioms scalar_support
#print axioms all_calls_support
#print axioms tower_support
end R1Z.ProverCommitReferenceReads
