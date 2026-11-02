import PV_EVH_NativeEntropyReturn
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyReturnSource
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_NativeEntropyIteration (buffer)
open PV_EVH_StackZero (Slot State Cleared)
open PV_EVH_StackCleanup (Q sameKey)
open PV_EVH_EntropyDecision (Accepted)

theorem source_accepted (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (a : Array U8 64#usize),
      retry < limit → getrandom.fill buffer = .ok (.Ok (),Array.to_slice a) →
      aspis_prover.state_only_entropy.entropy_nonzero32 (PV_EVH_EntropyHalves.field a) = .ok true →
      aspis_prover.state_only_entropy.entropy_nonzero32 (PV_EVH_EntropyHalves.seed a) = .ok true →
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = .ok (Accepted mask a) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry a hr hd hf hs
  rw [PV_EVH_NativeEntropyFilled.source_filled base heap box ops mask limit retry a hr hd]
  simp only [PV_EVH_NativeEntropyValues.tests,hf,hs,bind_tc_ok,if_true,
    Pure.pure,Accepted]

/-- Join the original SOURCE success branch at opsNative to the native
return-place move and deployed original64 cleanup. Actual move implementation,
its original-slot provenance, and physical copying of both32 remain explicit P.
The two nonzero tests are branch guards, not an actual successful-run witness. -/
theorem returned_source (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (a : Array U8 64#usize)
      (original field seed : Slot)
      (move : Slot → Slot → aspis_prover.state_only_entropy.StateOnlyAttemptSecrets → Q Unit)
      (w : State),
      retry < limit → getrandom.fill buffer = .ok (.Ok (),Array.to_slice a) →
      aspis_prover.state_only_entropy.entropy_nonzero32 (PV_EVH_EntropyHalves.field a) = .ok true →
      aspis_prover.state_only_entropy.entropy_nonzero32 (PV_EVH_EntropyHalves.seed a) = .ok true →
      let m := move field seed ⟨mask,PV_EVH_EntropyHalves.field a,PV_EVH_EntropyHalves.seed a⟩ w
      m.outcome = .returned (.ok ()) →
      m.state.frame.live.find? (sameKey original.key) = some original →
      original.initialized = 64 →
      let r := PV_EVH_NativeEntropyReturn.finish original.key field seed mask a move w
      PV_EVH_Runtime.sourceProjection r.outcome = some
        (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
          mask limit retry) ∧
      Cleared original r.state ∧
      r.events = m.events ++ PV_EVH_StackZero.emitted original ∧
      r.state.writes = m.state.writes+64 ∧ r.state.barriers = m.state.barriers+64 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry a original field seed move w hr hd hf hs
  dsimp only
  intro hm hl hn
  rw [PV_EVH_NativeEntropyReturn.returned_world original field seed mask a move w hm hl hn,
    source_accepted base heap box ops mask limit retry a hr hd hf hs]
  have hc := PV_EVH_EntropyCleanupCounts.drop_counts original
    (move field seed ⟨mask,PV_EVH_EntropyHalves.field a,PV_EVH_EntropyHalves.seed a⟩ w).state
  rw [hn] at hc
  exact ⟨rfl,PV_EVH_StackZero.dropped_cleared original _,rfl,hc.1,hc.2.1⟩

#print axioms source_accepted
#print axioms returned_source
end PV_EVH_NativeEntropyReturnSource
