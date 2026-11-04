import PV_EVH_NativeEntropyDelivered
import PV_EVH_EntropyRejectDelivery
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyRejected
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (State)
open PV_EVH_EntropyDeployedLayout (original entered)
open PV_EVH_NativeEntropyIteration (initial buffer)
open PV_EVH_NativeRawSelection (rawBase atWorld)

/-- Source rejection, complete physical fill and original-key cleanup are
joined at the SAME reached native dictionary/history. The guards are the two
actual short-circuited source tests, not a supplied whole-helper Result.
Actual primitive observations and an advancing full-entry family remain P. -/
theorem rejected_source_and_cleanup (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base))) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize)
      (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
      (memory : PV_EVH_RawMemoryHistory.MemoryAnswer) (owner sp fuel : Nat) (w : State),
      let history := PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
        sp fuel 0 initial w.frame.runtime.base
      let d := PV_EVH_LinuxRawControl.driver (fun code => code)
        (PV_EVH_LinuxRawObserve.call kernel) sp fuel buffer w
      retry < limit → history.delivery.status = .returned (.ok (.Ok ())) →
      PV_EVH_KernelMemory.ValidAnswer (PV_EVH_LinuxRawObserve.call kernel) memory sp →
      letI : ExternalFuns := opsNative (rawBase base) heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      (aspis_prover.state_only_entropy.entropy_nonzero32
          (PV_EVH_EntropyHalves.field history.delivery.buffer) = .ok false ∨
       (aspis_prover.state_only_entropy.entropy_nonzero32
          (PV_EVH_EntropyHalves.field history.delivery.buffer) = .ok true ∧
        aspis_prover.state_only_entropy.entropy_nonzero32
          (PV_EVH_EntropyHalves.seed history.delivery.buffer) = .ok false)) →
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = .ok (PV_EVH_EntropyDecision.Rejected retry) ∧
      PV_EVH_RawMemoryHistory.replay memory history.calls (entered owner sp w).memory =
        (PV_EVH_StackEntropyFill.post (original owner sp w) d (entered owner sp w)).memory ∧
      PV_EVH_EntropyRejectDelivery.checked owner sp w (PV_EVH_EntropyMoveKeys.ready owner sp d w) =
        ⟨.returned (.ok ()),PV_EVH_EntropyRejectDelivery.completed owner sp d w,
          PV_EVH_StackZero.emitted (PV_EVH_EntropyDeployedLayout.seed owner sp w) ++
          PV_EVH_StackZero.emitted (PV_EVH_EntropyDeployedLayout.field owner sp w) ++
          PV_EVH_StackZero.emitted (original owner sp w)⟩ ∧
      (original owner sp w).key.identity <
        (original owner sp (PV_EVH_EntropyRejectDelivery.completed owner sp d w)).key.identity := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry kernel memory owner sp fuel w
  dsimp only
  intro hr hd hk
  let d := PV_EVH_LinuxRawControl.driver (fun code => code)
    (PV_EVH_LinuxRawObserve.call kernel) sp fuel buffer w
  letI : ExternalFuns := opsNative (rawBase base) heap box
    (PV_EVH_ZeroWrappers.selected (atWorld ops d))
  intro hzero
  refine ⟨?_,PV_EVH_NativeEntropyDelivered.physical_fill (fun code => code)
    kernel memory owner sp fuel w hk,PV_EVH_EntropyRejectDelivery.checked_run owner sp d w,
    PV_EVH_EntropyRejectDelivery.next_original_fresh owner sp d w⟩
  rw [PV_EVH_NativeRawFinished.source_from_history base heap box ops
    mask limit retry kernel sp fuel w hr hd]
  rcases hzero with hf | ⟨hf,hs⟩
  · simp only [PV_EVH_NativeEntropyValues.tests,hf,bind_tc_ok,Bool.false_eq_true,
      if_false,PV_EVH_EntropyDecision.Rejected,Pure.pure]
  · simp only [PV_EVH_NativeEntropyValues.tests,hf,hs,bind_tc_ok,Bool.false_eq_true,
      if_true,if_false,PV_EVH_EntropyDecision.Rejected,Pure.pure]

#print axioms rejected_source_and_cleanup
end PV_EVH_NativeEntropyRejected
