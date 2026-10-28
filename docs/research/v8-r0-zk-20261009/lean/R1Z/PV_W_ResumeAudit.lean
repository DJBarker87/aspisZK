import R1Z.PV_W_Enriched
import R1Z.PV_W_EntryThreading
import R1Z.PV_W_ErrorSyntax
import R1Z.PV_W_FileDecode
import R1Z.PV_W_OsCombined
import R1Z.PV_W_OsEntropy
import R1Z.PV_W_OsFile
import R1Z.PV_W_OsSchedule
import R1Z.PV_W_ProverEntry
import R1Z.PV_W_RepeatFile
import R1Z.PV_W_Reservation
import R1Z.PV_W_ReservationThreading
import R1Z.PV_W_SourceSyntax
import R1Z.PV_W_StepTransport
import R1Z.PV_W_Syntax
import R1Z.PV_W_SyntaxMap
import R1Z.PV_W_Threading
import R1Z.PV_W_TypedEffects
import R1Z.PV_W_TypedReservation
import R1Z.PV_W_TypedThreading
import R1Z.PV_RunJoin_NativeEffectTransport
import R1Z.PV_RunJoin_OsWorldFrames
set_option autoImplicit false

/- Focused model/source frontier only; native/deployment target remains open. -/
#print axioms R1Z.PV_W_Enriched.drop_counter
#print axioms R1Z.PV_W_Enriched.drop_flag
#print axioms R1Z.PV_W_Enriched.drop_os_frame
#print axioms R1Z.PV_W_Enriched.drop_result
#print axioms R1Z.PV_W_Enriched.witness_representable
#print axioms R1Z.PV_W_Enriched.drop_valid
#print axioms R1Z.PV_W_Enriched.project_append
#print axioms R1Z.PV_W_Enriched.project_threaded
#print axioms R1Z.PV_W_EntryThreading.entry_source
#print axioms R1Z.PV_W_EntryThreading.entry_threads
#print axioms R1Z.PV_W_EntryThreading.entry_operational
#print axioms R1Z.PV_W_ErrorSyntax.error_bind
#print axioms R1Z.PV_W_ErrorSyntax.error_eval
#print axioms R1Z.PV_W_ErrorSyntax.error_frame
#print axioms R1Z.PV_W_FileDecode.decoded_matched
#print axioms R1Z.PV_W_FileDecode.decoded_rejected
#print axioms R1Z.PV_W_FileDecode.decoded_valid
#print axioms R1Z.PV_W_FileDecode.decoded_effect_prefix
#print axioms R1Z.PV_W_OsCombined.silent_frame
#print axioms R1Z.PV_W_OsCombined.visible_step
#print axioms R1Z.PV_W_OsCombined.file_valid
#print axioms R1Z.PV_W_OsCombined.draw_valid
#print axioms R1Z.PV_W_OsCombined.time_valid
#print axioms R1Z.PV_W_OsCombined.worker_valid
#print axioms R1Z.PV_W_OsCombined.reservation_full
#print axioms R1Z.PV_W_OsCombined.reservation_os
#print axioms R1Z.PV_W_OsEntropy.draw_at
#print axioms R1Z.PV_W_OsEntropy.draw_rejected
#print axioms R1Z.PV_W_OsEntropy.draw_valid
#print axioms R1Z.PV_W_OsEntropy.draw_complete_reply
#print axioms R1Z.PV_W_OsFile.file_matched
#print axioms R1Z.PV_W_OsFile.file_rejected
#print axioms R1Z.PV_W_OsFile.file_valid
#print axioms R1Z.PV_W_OsFile.file_failure_prefix
#print axioms R1Z.PV_W_OsSchedule.time_matched
#print axioms R1Z.PV_W_OsSchedule.worker_matched
#print axioms R1Z.PV_W_OsSchedule.time_valid
#print axioms R1Z.PV_W_OsSchedule.worker_valid
#print axioms R1Z.PV_W_ProverEntry.erase_maskedAttempt
#print axioms R1Z.PV_W_RepeatFile.first_step
#print axioms R1Z.PV_W_RepeatFile.second_step
#print axioms R1Z.PV_W_RepeatFile.first_call
#print axioms R1Z.PV_W_RepeatFile.second_call
#print axioms R1Z.PV_W_RepeatFile.repeated_exact
#print axioms R1Z.PV_W_RepeatFile.retained_world
#print axioms R1Z.PV_W_Reservation.erase_syncDirectory
#print axioms R1Z.PV_W_Reservation.erase_reserveFallible
#print axioms R1Z.PV_W_Reservation.erase_reserve
#print axioms R1Z.PV_W_ReservationThreading.source_complete
#print axioms R1Z.PV_W_ReservationThreading.reservation_exact
#print axioms R1Z.PV_W_ReservationThreading.reservation_constructed
#print axioms R1Z.PV_W_ReservationThreading.reservation_projection
#print axioms R1Z.PV_W_SourceSyntax.erase_invoke
#print axioms R1Z.PV_W_SourceSyntax.erase_thenDo
#print axioms R1Z.PV_W_SourceSyntax.erase_bind
#print axioms R1Z.PV_W_SourceSyntax.source_bind_congr
#print axioms R1Z.PV_W_SourceSyntax.erase_pure
#print axioms R1Z.PV_W_SourceSyntax.erase_coreResult
#print axioms R1Z.PV_W_SourceSyntax.erase_controlFlow
#print axioms R1Z.PV_W_SourceSyntax.erase_ite
#print axioms R1Z.PV_W_SourceSyntax.source_value
#print axioms R1Z.PV_W_StepTransport.threaded_mono
#print axioms R1Z.PV_W_StepTransport.valid_mono
#print axioms R1Z.PV_W_Syntax.eval_thenDo
#print axioms R1Z.PV_W_Syntax.execution_sound
#print axioms R1Z.PV_W_Syntax.execution_complete
#print axioms R1Z.PV_W_Syntax.eval_valid
#print axioms R1Z.PV_W_Syntax.execution_exact
#print axioms R1Z.PV_W_SyntaxMap.map_bind
#print axioms R1Z.PV_W_SyntaxMap.eval_map
#print axioms R1Z.PV_W_Threading.lift_frame
#print axioms R1Z.PV_W_Threading.lift_bind
#print axioms R1Z.PV_W_Threading.bind_ok
#print axioms R1Z.PV_W_Threading.bind_fail
#print axioms R1Z.PV_W_Threading.bind_div
#print axioms R1Z.PV_W_Threading.bind_assoc
#print axioms R1Z.PV_W_Threading.threaded_append
#print axioms R1Z.PV_W_Threading.valid_lift
#print axioms R1Z.PV_W_Threading.valid_emit
#print axioms R1Z.PV_W_Threading.valid_bind
#print axioms R1Z.PV_W_Threading.no_lift_advancing
#print axioms R1Z.PV_W_Threading.no_trace_decoder
#print axioms R1Z.PV_W_TypedEffects.erase_bind
#print axioms R1Z.PV_W_TypedEffects.erase_perform
#print axioms R1Z.PV_W_TypedEffects.erase_invoke
#print axioms R1Z.PV_W_TypedEffects.erase_pure
#print axioms R1Z.PV_W_TypedReservation.erase_syncDirectory
#print axioms R1Z.PV_W_TypedReservation.erase_reserveFallible
#print axioms R1Z.PV_W_TypedReservation.erase_reserve
#print axioms R1Z.PV_W_TypedThreading.primitive_valid
#print axioms R1Z.PV_W_TypedThreading.reservation_threads
#print axioms R1Z.PV_W_TypedThreading.reservation_operational
#print axioms R1Z.PV_W_TypedThreading.source_complete
