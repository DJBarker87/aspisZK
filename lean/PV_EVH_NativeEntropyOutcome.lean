import PV_EVH_EntropyDecision
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyOutcome
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_NativeEntropyIteration (buffer initial)
open PV_EVH_StackZero (State)
open PV_EVH_NativeRawSelection (rawBase atWorld)

/-- Every COMPLETED raw fill gives a total source iteration at the reached
native dictionary. This discharges source-test/copy failure on this branch,
not actual fill completion, original frame admission, native moves/retries,
full-entry success, or observation/allocator adequacy. -/
theorem source_outcome (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base))) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize)
      (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
      (address fuel : Nat) (w : State),
      let history := PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
        address fuel 0 initial w.frame.runtime.base
      let d := PV_EVH_LinuxRawControl.driver (fun code => code)
        (PV_EVH_LinuxRawObserve.call kernel) address fuel buffer w
      retry < limit → history.delivery.status = .returned (.ok (.Ok ())) →
      letI : ExternalFuns := opsNative (rawBase base) heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      ∃ out, aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = .ok out ∧
        (out = PV_EVH_EntropyDecision.Rejected retry ∨
          out = PV_EVH_EntropyDecision.Accepted mask history.delivery.buffer) := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry kernel address fuel w
  dsimp only
  intro hr hs
  let d := PV_EVH_LinuxRawControl.driver (fun code => code)
    (PV_EVH_LinuxRawObserve.call kernel) address fuel buffer w
  letI : ExternalFuns := opsNative (rawBase base) heap box
    (PV_EVH_ZeroWrappers.selected (atWorld ops d))
  rw [PV_EVH_NativeRawFinished.source_from_history base heap box ops
    mask limit retry kernel address fuel w hr hs]
  exact PV_EVH_EntropyDecision.tests_total mask retry _

#print axioms source_outcome
end PV_EVH_NativeEntropyOutcome
