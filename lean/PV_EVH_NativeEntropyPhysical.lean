import PV_EVH_EntropyPhysicalCopy
import PV_EVH_NativeRawFinished
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyPhysical
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (Slot State)
open PV_EVH_NativeEntropyIteration (buffer initial)
open PV_EVH_NativeRawSelection (rawBase atWorld)

/-- SAME raw delivery supplies the original extracted source tests and both
physical copy destinations. No per-half memory answer is a premise. This is
conditional on actual frame separation and byte-copy primitive association;
it is not an actual successful prover witness or a full-entry adequacy law. -/
theorem source_and_backing (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base))) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize)
      (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
      (original field seed : Slot) (fuel : Nat) (w : State),
      let history := PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
        original.address fuel 0 initial w.frame.runtime.base
      let d := PV_EVH_LinuxRawControl.driver (fun code => code)
        (PV_EVH_LinuxRawObserve.call kernel) original.address fuel buffer w
      let v := PV_EVH_EntropyPhysicalCopy.copies original field seed
        (PV_EVH_EntropyPhysicalCopy.admit_pair field seed
          (PV_EVH_StackEntropyFill.post original d w))
      retry < limit → history.delivery.status = .returned (.ok (.Ok ())) →
      original.initialized = 64 → field.initialized = 32 → seed.initialized = 32 →
      PV_EVH_StackRegions.Separate field original →
      PV_EVH_StackRegions.Separate seed original →
      PV_EVH_StackRegions.Separate seed field →
      letI : ExternalFuns := opsNative (rawBase base) heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = PV_EVH_NativeEntropyValues.tests mask retry history.delivery.buffer) ∧
      (∀ i, i < 32 → v.memory (field.address+i) =
        ((PV_EVH_StackEntropyFill.encode history.delivery.buffer)[i]?.getD 0).toNat) ∧
      (∀ i, i < 32 → v.memory (seed.address+i) =
        ((PV_EVH_StackEntropyFill.encode history.delivery.buffer)[32+i]?.getD 0).toNat) := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry kernel original field seed fuel w
  dsimp only
  intro hr hd ho hf hs hfo hso hsf
  have hbody := PV_EVH_NativeRawFinished.source_from_history base heap box ops
    mask limit retry kernel original.address fuel w hr hd
  have halves := PV_EVH_EntropyPhysicalCopy.delivered_halves original field seed
    (PV_EVH_StackEntropyFill.post original
      (PV_EVH_LinuxRawControl.driver (fun code => code) (PV_EVH_LinuxRawObserve.call kernel)
        original.address fuel buffer w) w)
    _ ho hf hs hfo hso hsf
    (fun i hi => PV_EVH_StackEntropyFill.physical_buffer original _ w i (by omega))
  have hb := (PV_EVH_NativeRawFinished.driver_delivery (fun code => code)
    kernel original.address fuel w).2.1
  rw [hb] at halves
  exact ⟨hbody,halves⟩

#print axioms source_and_backing
end PV_EVH_NativeEntropyPhysical
