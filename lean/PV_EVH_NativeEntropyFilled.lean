import PV_EVH_NativeEntropyValues
import PV_EVH_NativeEntropyIteration
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyFilled
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_NativeEntropyIteration (buffer initial restore)

/-- The ORIGINAL extracted loop-body on a completed fill. Both half-array
restorations are discharged at opsNative; actual physical frame/kernel and
native success/retry/move interpretation remain separate obligations. -/
theorem source_filled (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (mask : Array U8 32#usize) (limit retry : Usize) (a : Array U8 64#usize),
      retry < limit → getrandom.fill buffer = .ok (.Ok (),Array.to_slice a) →
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = PV_EVH_NativeEntropyValues.tests mask retry a := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro mask limit retry a hr hf
  simp only [aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body,
    hr,if_true]
  rw [PV_EVH_NativeZeroWrappers.constructor_native base heap box ops]
  simp only [bind_tc_ok]
  rw [PV_EVH_NativeEntropyBorrow.array_borrow base heap box ops]
  simp only [bind_tc_ok]
  change (do let (r,s) ← getrandom.fill buffer
             PV_EVH_Entropy.afterDraw mask retry restore r s) = _
  rw [hf]
  exact PV_EVH_NativeEntropyValues.after_draw base heap box ops mask retry initial a

#print axioms source_filled
end PV_EVH_NativeEntropyFilled
