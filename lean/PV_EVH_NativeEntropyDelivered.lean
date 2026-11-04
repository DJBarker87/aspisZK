import PV_EVH_RawMemoryReification
import PV_EVH_EntropyReturnDelivery
import PV_EVH_NativeEntropyReturnSource
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyDelivered
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_StackZero (State)
open PV_EVH_EntropyDeployedLayout (original entered)
open PV_EVH_EntropyCallerLayout (mask result)
open PV_EVH_NativeEntropyIteration (initial buffer)
open PV_EVH_NativeRawSelection (rawBase atWorld)

/-- The source zero initializer, symbolically; no concrete scan/recurrence is
normalized to establish physical entry backing. -/
theorem initial_encoding :
    PV_EVH_StackEntropyFill.encode initial = List.replicate 64 0 := by
  simp only [PV_EVH_StackEntropyFill.encode,initial,Array.repeat,List.map_replicate]
  rfl

/-- Full raw-history memory reification at the actual source-shaped entry,
with no independent pre-buffer or post-buffer premise. The actual OS instance
of ValidAnswer and the runtime/compiler FRAME association remain P. -/
theorem physical_fill [ExternalTypes] (decode : Int → getrandom.error.Error)
    (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
    (memory : PV_EVH_RawMemoryHistory.MemoryAnswer) (owner sp fuel : Nat) (w : State)
    (hk : PV_EVH_KernelMemory.ValidAnswer (PV_EVH_LinuxRawObserve.call kernel) memory sp) :
    let history := PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
      sp fuel 0 initial w.frame.runtime.base
    let d := PV_EVH_LinuxRawControl.driver decode
      (PV_EVH_LinuxRawObserve.call kernel) sp fuel buffer w
    PV_EVH_RawMemoryHistory.replay memory history.calls (entered owner sp w).memory =
      (PV_EVH_StackEntropyFill.post (original owner sp w) d (entered owner sp w)).memory := by
  dsimp only
  have hb := PV_EVH_RawMemoryReification.admitted (original owner sp w) initial w rfl
  rw [initial_encoding] at hb
  exact PV_EVH_RawMemoryReification.driver_memory decode
    (PV_EVH_LinuxRawObserve.call kernel) memory (original owner sp w) fuel buffer
    (entered owner sp w) rfl hk hb

/-- The reached original source acceptance and every returned payload byte
come from ONE raw history and the original ENTRY mask. No helper Result,
copy/move answer, post-move key lookup, or per-lane entropy answer is supplied.
This is source/physical integration, not an installed native observation family:
read/store/register/spill observations, actual FRAME and KERNEL-WRITE remain P. -/
theorem successful_source_and_bytes (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
    (ops : @ExternalFuns (types (rawBase base))) :
    letI : ExternalTypes := types (rawBase base)
    ∀ (sourceMask : Array U8 32#usize) (limit retry : Usize)
      (kernel : Nat → Nat → Array U8 64#usize → PV_EVH_World.World → PV_EVH_LinuxRawControl.Reply)
      (memory : PV_EVH_RawMemoryHistory.MemoryAnswer) (owner sp fuel : Nat) (w : State),
      let history := PV_EVH_LinuxRawHistory.execute (PV_EVH_LinuxRawObserve.call kernel)
        sp fuel 0 initial w.frame.runtime.base
      let d := PV_EVH_LinuxRawControl.driver (fun code => code)
        (PV_EVH_LinuxRawObserve.call kernel) sp fuel buffer w
      retry < limit → history.delivery.status = .returned (.ok (.Ok ())) →
      PV_EVH_KernelMemory.ValidAnswer (PV_EVH_LinuxRawObserve.call kernel) memory sp →
      (∀ i, i < 32 → w.memory (mask sp+i) =
        ((PV_EVH_StackEntropyFill.encode sourceMask)[i]?.getD 0).toNat) →
      letI : ExternalFuns := opsNative (rawBase base) heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      aspis_prover.state_only_entropy.entropy_nonzero32
        (PV_EVH_EntropyHalves.field history.delivery.buffer) = .ok true →
      aspis_prover.state_only_entropy.entropy_nonzero32
        (PV_EVH_EntropyHalves.seed history.delivery.buffer) = .ok true →
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        sourceMask limit retry = .ok (PV_EVH_EntropyDecision.Accepted sourceMask history.delivery.buffer) ∧
      PV_EVH_RawMemoryHistory.replay memory history.calls (entered owner sp w).memory =
        (PV_EVH_StackEntropyFill.post (original owner sp w) d (entered owner sp w)).memory ∧
      ∀ i, i < 32 →
        let out := PV_EVH_EntropyReturnDelivery.completed owner sp d w
        out.memory (result sp) = 0 ∧
        out.memory (result sp+1+i) =
          ((PV_EVH_StackEntropyFill.encode sourceMask)[i]?.getD 0).toNat ∧
        out.memory (result sp+33+i) =
          ((PV_EVH_StackEntropyFill.encode history.delivery.buffer)[i]?.getD 0).toNat ∧
        out.memory (result sp+65+i) =
          ((PV_EVH_StackEntropyFill.encode history.delivery.buffer)[32+i]?.getD 0).toNat := by
  letI : ExternalTypes := types (rawBase base)
  intro sourceMask limit retry kernel memory owner sp fuel w
  dsimp only
  intro hr hd hk hm
  let d := PV_EVH_LinuxRawControl.driver (fun code => code)
    (PV_EVH_LinuxRawObserve.call kernel) sp fuel buffer w
  letI : ExternalFuns := opsNative (rawBase base) heap box
    (PV_EVH_ZeroWrappers.selected (atWorld ops d))
  intro hf hs
  have hsource := PV_EVH_NativeRawFinished.source_from_history base heap box ops
    sourceMask limit retry kernel sp fuel w hr hd
  have hbuffer := (PV_EVH_NativeRawFinished.driver_delivery (fun code => code)
    kernel sp fuel w).2.1
  refine ⟨?_,physical_fill (fun code => code) kernel memory owner sp fuel w hk,?_⟩
  · rw [hsource]
    simp only [PV_EVH_NativeEntropyValues.tests,hf,hs,bind_tc_ok,if_true,
      PV_EVH_EntropyDecision.Accepted,Pure.pure]
  · intro i hi
    have h := PV_EVH_EntropyReturnDelivery.returned_delivery owner sp d w i hi
    rw [hm i hi] at h
    change d.buffer = _ at hbuffer
    rw [hbuffer] at h
    exact h

#print axioms initial_encoding
#print axioms physical_fill
#print axioms successful_source_and_bytes
end PV_EVH_NativeEntropyDelivered
