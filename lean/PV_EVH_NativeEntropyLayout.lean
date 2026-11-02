import PV_EVH_EntropyDeployedLayout
import PV_EVH_NativeEntropyPhysical
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyLayout
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (State)
open PV_EVH_NativeEntropyIteration (buffer initial)
open PV_EVH_NativeRawSelection (rawBase atWorld)
open PV_EVH_EntropyDeployedLayout (original field seed)

/-- Existing original-source/native law with all six local FRAME hypotheses
discharged for the adopted offsets. FRAME-CALL/V370 and KERNEL-WRITE still bind
this memory interpretation to an actual reached invocation and kernel; the
statement does not assert that an arbitrary State is a real machine frame. -/
theorem source_and_backing (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base))) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize)
      (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
      (owner sp fuel : Nat) (w : State),
      let o := original owner sp w
      let f := field owner sp w
      let s := seed owner sp w
      let history := PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
        o.address fuel 0 initial w.frame.runtime.base
      let d := PV_EVH_LinuxRawControl.driver (fun code => code)
        (PV_EVH_LinuxRawObserve.call kernel) o.address fuel buffer w
      let v := PV_EVH_EntropyPhysicalCopy.copies o f s
        (PV_EVH_EntropyPhysicalCopy.admit_pair f s
          (PV_EVH_StackEntropyFill.post o d w))
      retry < limit → history.delivery.status = .returned (.ok (.Ok ())) →
      letI : ExternalFuns := opsNative (rawBase base) heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = PV_EVH_NativeEntropyValues.tests mask retry history.delivery.buffer) ∧
      (∀ i, i < 32 → v.memory (f.address+i) =
        ((PV_EVH_StackEntropyFill.encode history.delivery.buffer)[i]?.getD 0).toNat) ∧
      (∀ i, i < 32 → v.memory (s.address+i) =
        ((PV_EVH_StackEntropyFill.encode history.delivery.buffer)[32+i]?.getD 0).toNat) := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry kernel owner sp fuel w
  dsimp only
  intro hr hd
  have h := PV_EVH_EntropyDeployedLayout.separation owner sp w
  exact PV_EVH_NativeEntropyPhysical.source_and_backing base heap box ops
    mask limit retry kernel (original owner sp w) (field owner sp w)
    (seed owner sp w) fuel w hr hd rfl rfl rfl h.1 h.2.1 h.2.2

#print axioms source_and_backing
end PV_EVH_NativeEntropyLayout
