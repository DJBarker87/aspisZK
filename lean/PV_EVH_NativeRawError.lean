import PV_EVH_NativeRawSelection
import PV_EVH_NativeLinuxError
import PV_EVH_EntropySourceSlot
import PV_EVH_LinuxRawCodes
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeRawError
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (State Cleared)
open PV_EVH_StackCleanup (Q)
open PV_EVH_NativeEntropyError (Answer)
open PV_EVH_NativeEntropyIteration (buffer initial run)
open PV_EVH_NativeRawSelection (rawBase atWorld)

theorem status_identity (base : ExternalTypes)
    (s : PV_EVH_Runtime.Outcome (core.result.Result Unit Int)) :
    letI : ExternalTypes := types (rawBase base)
    PV_EVH_LinuxRawControl.status (fun code => code) s = s := by
  letI : ExternalTypes := types (rawBase base)
  cases s with
  | fault e => rfl
  | exhausted => rfl
  | returned r =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok r =>
      cases r with
      | Err e => rfl
      | Ok u => cases u; rfl

theorem raw_code (base : ExternalTypes)
    (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
    (address fuel : Nat) (w : State) (e : Int) :
    letI : ExternalTypes := types (rawBase base)
    (PV_EVH_LinuxRawControl.driver (fun code => code)
      (PV_EVH_LinuxRawObserve.call kernel) address fuel buffer w).status =
      .returned (.ok (.Err e)) → PV_EVH_LinuxRawCodes.ValidCode e := by
  letI : ExternalTypes := types (rawBase base)
  intro h
  change PV_EVH_LinuxRawControl.status (fun code => code)
    (PV_EVH_LinuxRawControl.loop (PV_EVH_LinuxRawObserve.call kernel) address fuel 0
      (Array.repeat 64#usize 0#u8) w.frame.runtime.base).status = _ at h
  rw [status_identity base] at h
  exact PV_EVH_LinuxRawCodes.all_codes (PV_EVH_LinuxRawObserve.call kernel)
    address fuel 0 (Array.repeat 64#usize 0#u8) w.frame.runtime.base e h

/-- Actual extracted error iteration at opsNative with world-specific op129.
No driver heap-equality, source-fill equality, fresh-key or extent hypothesis is
needed. The original address's spatial provenance and initial heap coherence
remain P. This is not full entry adequacy or a uniform entropy dictionary view.
Deployed zeroize1.9.0 still supplies cleanup and its L3-observable history. -/
theorem error_connected (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base))) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (owner address : Nat)
      (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
      (fuel : Nat)
      (success : (Slice U8 → zeroize.Zeroizing (Array U8 64#usize)) → Slice U8 → Q Answer)
      (w : State) (e : Int),
      let slot := PV_EVH_EntropySourceSlot.original owner address w
      let driver := PV_EVH_LinuxRawControl.driver (fun code => code)
        (PV_EVH_LinuxRawObserve.call kernel) address fuel
      let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
      let d := driver buffer wi
      retry < limit →
      PV_EVH_StackAdmission.HeapSeparate slot w →
      PV_EVH_StackAdmission.LiveSeparate slot w →
      PV_EVH_StackAdmission.HeapCoherent w →
      d.status = .returned (.ok (.Err e)) →
      letI : ExternalFuns := opsNative (rawBase base) heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      let r := run mask limit retry slot driver success w
      PV_EVH_Runtime.sourceProjection r.outcome = some
        (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
          mask limit retry) ∧
      Cleared slot r.state ∧ PV_EVH_LinuxRawCodes.ValidCode e ∧
      PV_EVH_StackAdmission.HeapCoherent r.state ∧
      r.state.frame.live = w.frame.live ∧
      r.events = d.events ++ PV_EVH_StackZero.emitted slot := by
  letI : ExternalTypes := types (rawBase base)
  intro mask limit retry owner address kernel fuel success w e
  dsimp only
  intro hr hs hl hc hd
  let slot := PV_EVH_EntropySourceSlot.original owner address w
  let driver := PV_EVH_LinuxRawControl.driver (fun code => code)
    (PV_EVH_LinuxRawObserve.call kernel) address fuel
  let wi := PV_EVH_StackAdmission.enter slot (PV_EVH_StackEntropyFill.encode initial) w
  let d := driver buffer wi
  let ops' := atWorld ops d
  letI : ExternalFuns := opsNative (rawBase base) heap box (PV_EVH_ZeroWrappers.selected ops')
  have ha := PV_EVH_EntropySourceSlot.admission owner address w hs hl
  have hf := PV_EVH_NativeRawSelection.error_fill (rawBase base) heap box ops d e hd
  have hfull := PV_EVH_NativeEntropyIterationError.error_native (rawBase base) heap box
    ops' mask limit retry slot driver success w e hr rfl hd hf
  have hcoh := PV_EVH_NativeLinuxError.error_coherent (rawBase base) heap box ops'
    mask limit retry slot (fun code => code) kernel fuel success w e hr ha hc hd
  exact ⟨hfull.1,hfull.2.1,raw_code base kernel address fuel wi e hd,
    hcoh.1,hcoh.2,hfull.2.2.2.2.2⟩

#print axioms status_identity
#print axioms raw_code
#print axioms error_connected
end PV_EVH_NativeRawError
