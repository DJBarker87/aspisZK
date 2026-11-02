import PV_EVH_NativeRawSuccess
import PV_EVH_LinuxRawHistory
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeRawFinished
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_NativeEntropyIteration (buffer initial)
open PV_EVH_StackZero (State)
open PV_EVH_NativeRawSelection (rawBase atWorld)

theorem driver_delivery [ExternalTypes] (decode : Int → getrandom.error.Error)
    (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
    (address fuel : Nat) (w : State) :
    let h := PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
      address fuel 0 initial w.frame.runtime.base
    let d := PV_EVH_LinuxRawControl.driver decode (PV_EVH_LinuxRawObserve.call kernel)
      address fuel buffer w
    d.status = PV_EVH_LinuxRawControl.status decode h.delivery.status ∧
    d.buffer = h.delivery.buffer ∧ d.runtime.base = h.delivery.world ∧
    d.events = h.delivery.events := by
  dsimp only
  unfold PV_EVH_LinuxRawControl.driver
  rw [← PV_EVH_LinuxRawHistory.erases]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The actual source continuation consumes exactly the delivered buffer from
the existing raw syscall history. A completed fill may still reject zero
halves; this theorem does not infer a successful proof or a fixed dictionary
across different entropy worlds. Frame/kernel/move/L3 association remains P. -/
theorem source_from_history (base : ExternalTypes)
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
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = PV_EVH_NativeEntropyValues.tests mask retry history.delivery.buffer := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry kernel address fuel w
  dsimp only
  intro hr hs
  have h := driver_delivery (fun code => code) kernel address fuel w
  have hd := h.1
  rw [hs] at hd
  change _ = PV_EVH_LinuxRawControl.status (fun code => code)
    (.returned (.ok (.Ok ()))) at hd
  have hi := PV_EVH_NativeRawSuccess.source_body (rawBase base) heap box ops
    mask limit retry _ hr hd
  rw [h.2.1] at hi
  exact hi

#print axioms driver_delivery
#print axioms source_from_history
end PV_EVH_NativeRawFinished
