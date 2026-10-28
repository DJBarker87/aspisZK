import R1Z.PV_DL_CompressionTrace
import R1Z.PV_DL_Default
import R1Z.PV_DL_DefaultBuffer
import R1Z.PV_DL_DefaultCallback
import R1Z.PV_DL_DefaultLaw
import R1Z.PV_DL_DefaultNative
import R1Z.PV_DL_DefaultSelected
import R1Z.PV_DL_DefaultTypes
import R1Z.PV_DL_EncoderBasis
import R1Z.PV_DL_EncoderControl
import R1Z.PV_DL_EncoderFill
import R1Z.PV_DL_EncoderFold
import R1Z.PV_DL_EncoderPairs
import R1Z.PV_DL_EncoderRange
import R1Z.PV_DL_EncoderSelected
import R1Z.PV_DL_FinalizeParam
import R1Z.PV_DL_Forwarding
import R1Z.PV_DL_Truncation
import R1Z.PV_DL_UpdateEvents
import R1Z.PV_DL_Wrap
import R1Z.PV_DL_WrapLaw
import R1Z.PV_DL_WrapTypes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_Audit
set_option autoImplicit false
theorem unit_run {B : Type} (events : List B) :
    PV_DL_CompressionTrace.run (fun (_ : Unit) (_ : B) => ok ()) events ()=ok () := by
  induction events with
  | nil => rfl
  | cons b tail ih => simp only [PV_DL_CompressionTrace.run,bind_tc_ok,ih]

theorem padding_success (buffer : Array U8 64#usize) (pos : Usize)
    (suffix : Array U8 8#usize) (h : pos.val<64) :
    PV_DL_FinalizeParam.reference (fun (_ : Unit) (_ : List U8) => ok ()) () buffer pos suffix=
      ok ((),PV_CBL_PaddingModel.first buffer.val pos.val suffix.val,0) := by
  rw [PV_DL_FinalizeParam.source _ _ buffer pos suffix h]
  simp only [PV_DL_FinalizeParam.model,unit_run,bind_tc_ok]

theorem padding_domain : ∃ buffer : Array U8 64#usize, ∃ pos : Usize,
    ∃ suffix : Array U8 8#usize, pos.val<64 ∧
    PV_DL_FinalizeParam.reference (fun (_ : Unit) (_ : List U8) => ok ()) () buffer pos suffix=
      ok ((),PV_CBL_PaddingModel.first buffer.val pos.val suffix.val,0) :=
  ⟨Array.repeat 64#usize 0#u8,0#usize,Array.repeat 8#usize 0#u8,by decide,
    padding_success _ _ _ (by decide)⟩

#print axioms R1Z.PV_DL_CompressionTrace.run
#print axioms R1Z.PV_DL_CompressionTrace.empty
#print axioms R1Z.PV_DL_CompressionTrace.append
#print axioms R1Z.PV_DL_CompressionTrace.event_transport
#print axioms R1Z.PV_DL_CompressionTrace.backend_instances
#print axioms PV_DL_Default.default_reference
#print axioms R1Z.PV_DL_DefaultBuffer.zeroStorage
#print axioms R1Z.PV_DL_DefaultBuffer.initial
#print axioms R1Z.PV_DL_DefaultBuffer.model
#print axioms R1Z.PV_DL_DefaultBuffer.bytes
#print axioms R1Z.PV_DL_DefaultBuffer.success
#print axioms R1Z.PV_DL_DefaultBuffer.failure
#print axioms R1Z.PV_DL_DefaultBuffer.divergence
#print axioms R1Z.PV_DL_DefaultBuffer.nonvacuous
#print axioms R1Z.PV_DL_DefaultBuffer.position
#print axioms R1Z.PV_DL_DefaultCallback.Limit
#print axioms R1Z.PV_DL_DefaultCallback.size
#print axioms R1Z.PV_DL_DefaultCallback.callback
#print axioms R1Z.PV_DL_DefaultLaw.initialState
#print axioms R1Z.PV_DL_DefaultLaw.snapshot
#print axioms R1Z.PV_DL_DefaultLaw.source
#print axioms R1Z.PV_DL_DefaultLaw.nonvacuous
#print axioms R1Z.PV_DL_DefaultLaw.empty_position
#print axioms R1Z.PV_DL_DefaultLaw.zero_blocks
#print axioms R1Z.PV_DL_DefaultLaw.backend_independent
#print axioms R1Z.PV_DL_DefaultNative.bufferKind
#print axioms R1Z.PV_DL_DefaultNative.native_callback
#print axioms R1Z.PV_DL_DefaultNative.consumed
#print axioms R1Z.PV_DL_DefaultSelected.dispatch
#print axioms R1Z.PV_DL_DefaultSelected.dispatch_source
#print axioms R1Z.PV_DL_DefaultSelected.selected
#print axioms R1Z.PV_DL_EncoderBasis.advance
#print axioms R1Z.PV_DL_EncoderBasis.half_rank
#print axioms R1Z.PV_DL_EncoderBasis.advance_val
#print axioms R1Z.PV_DL_EncoderBasis.factor
#print axioms R1Z.PV_DL_EncoderBasis.finite
#print axioms R1Z.PV_DL_EncoderBasis.source
#print axioms R1Z.PV_DL_EncoderBasis.value
#print axioms R1Z.PV_DL_EncoderBasis.basis_source
#print axioms R1Z.PV_DL_EncoderBasis.native_min
#print axioms R1Z.PV_DL_EncoderControl.duplicate
#print axioms R1Z.PV_DL_EncoderControl.value
#print axioms R1Z.PV_DL_EncoderControl.source_reference
#print axioms R1Z.PV_DL_EncoderControl.inputs_nonempty
#print axioms R1Z.PV_DL_EncoderFill.finite
#print axioms R1Z.PV_DL_EncoderFill.source
#print axioms R1Z.PV_DL_EncoderFold.step
#print axioms R1Z.PV_DL_EncoderFold.finite
#print axioms R1Z.PV_DL_EncoderFold.source
#print axioms R1Z.PV_DL_EncoderPairs.chunks
#print axioms R1Z.PV_DL_EncoderPairs.length
#print axioms R1Z.PV_DL_EncoderPairs.coordinate
#print axioms R1Z.PV_DL_EncoderPairs.message_count
#print axioms R1Z.PV_DL_EncoderRange.advance
#print axioms R1Z.PV_DL_EncoderRange.advance_val
#print axioms R1Z.PV_DL_EncoderRange.even
#print axioms R1Z.PV_DL_EncoderRange.odd
#print axioms R1Z.PV_DL_EncoderSelected.selected
#print axioms R1Z.PV_DL_EncoderSelected.selected_callback
#print axioms R1Z.PV_DL_EncoderSelected.consumed
#print axioms R1Z.PV_DL_EncoderSelected.pairs_complete
#print axioms R1Z.PV_DL_FinalizeParam.reference
#print axioms R1Z.PV_DL_FinalizeParam.model
#print axioms R1Z.PV_DL_FinalizeParam.source
#print axioms R1Z.PV_DL_FinalizeParam.callback_count
#print axioms R1Z.PV_DL_Forwarding.output
#print axioms R1Z.PV_DL_Forwarding.failure
#print axioms R1Z.PV_DL_Forwarding.ct
#print axioms R1Z.PV_DL_Forwarding.ct_restoration
#print axioms R1Z.PV_DL_Forwarding.ct_length
#print axioms R1Z.PV_DL_Truncation.value
#print axioms R1Z.PV_DL_Truncation.length
#print axioms R1Z.PV_DL_Truncation.full
#print axioms R1Z.PV_DL_Truncation.left_source
#print axioms R1Z.PV_DL_Truncation.right_source
#print axioms R1Z.PV_DL_UpdateEvents.Plumbing
#print axioms R1Z.PV_DL_UpdateEvents.step
#print axioms R1Z.PV_DL_UpdateEvents.fold
#print axioms R1Z.PV_DL_UpdateEvents.append
#print axioms R1Z.PV_DL_UpdateEvents.complete
#print axioms R1Z.PV_DL_UpdateEvents.pending
#print axioms PV_DL_Wrap.wrap_reference
#print axioms R1Z.PV_DL_WrapLaw.observe
#print axioms R1Z.PV_DL_WrapLaw.observeReference
#print axioms R1Z.PV_DL_WrapLaw.source_reference
#print axioms unit_run
#print axioms padding_success
#print axioms padding_domain
end R1Z.PV_DL_Audit
