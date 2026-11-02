import PV_EVH_NativeEntropyFilled
import PV_EVH_NativeRawSelection
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeRawSuccess
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62
open PV_EVH_NativeEntropyIteration (buffer)
open PV_EVH_NativeRawSelection (atInput atWorld)

theorem input_success [ExternalTypes] (ops : ExternalFuns) (input : Slice U8)
    (d : PV_EVH_StackEntropyFill.Delivery)
    (hd : d.status = .returned (.ok (.Ok ()))) :
    @ExternalFuns.op129 _ (atInput ops input d) input =
      .ok (.Ok (),Array.to_slice d.buffer) := by
  change (if input = input then
    match PV_EVH_StackEntropyFill.reply d with
    | .returned r => r
    | _ => ops.op129 input
    else ops.op129 input) = _
  rw [if_pos rfl,PV_EVH_StackEntropyFill.reply,hd]
  rfl

/-- A reached-world installation, not one dictionary shared across distinct
draws. The successful delivery is a primitive answer, not an assumed prover
success or an answer for the whole generate_for_mask_nonce helper. -/
theorem fill_success (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    ∀ (d : PV_EVH_StackEntropyFill.Delivery),
      d.status = .returned (.ok (.Ok ())) →
      letI : ExternalFuns := opsNative base heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      getrandom.fill buffer = .ok (.Ok (),Array.to_slice d.buffer) := by
  letI : ExternalTypes := types base
  intro d hd
  change @ExternalFuns.op129 _ (atInput ops buffer d) buffer = _
  exact input_success ops buffer d hd

theorem source_body (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    ∀ (mask : Array U8 32#usize) (limit retry : Usize)
      (d : PV_EVH_StackEntropyFill.Delivery),
      retry < limit → d.status = .returned (.ok (.Ok ())) →
      letI : ExternalFuns := opsNative base heap box
        (PV_EVH_ZeroWrappers.selected (atWorld ops d))
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        mask limit retry = PV_EVH_NativeEntropyValues.tests mask retry d.buffer := by
  letI : ExternalTypes := types base
  intro mask limit retry d hr hd
  exact PV_EVH_NativeEntropyFilled.source_filled base heap box (atWorld ops d)
    mask limit retry d.buffer hr (fill_success base heap box ops d hd)

#print axioms input_success
#print axioms fill_success
#print axioms source_body
end PV_EVH_NativeRawSuccess
