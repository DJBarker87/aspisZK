import R1Z.PV_FXM_AuditAxioms
import R1Z.PV_W_Callbacks
import R1Z.PV_W_EnrichedMemory
import R1Z.PV_W_FromSemantics
import R1Z.PV_W_IfLaws
import R1Z.PV_W_Loops
import R1Z.PV_W_MaskedWithAttempt
import R1Z.PV_W_MemoryCombined
import R1Z.PV_W_MemoryLift
import R1Z.PV_W_Ownership
import R1Z.PV_W_PrivateSalts
import R1Z.PV_W_PrivateSaltsLoop
import R1Z.PV_W_R_ApplyMaterial
import R1Z.PV_W_R_AuditMasks
import R1Z.PV_W_R_AuditMasksBody0
import R1Z.PV_W_R_AuditMasksBody1
import R1Z.PV_W_R_DurableReserve
import R1Z.PV_W_R_Entry
import R1Z.PV_W_R_FinishOpening
import R1Z.PV_W_R_FixedColumn
import R1Z.PV_W_R_FromSemantics
import R1Z.PV_W_R_HostBuild
import R1Z.PV_W_R_InactiveSumBody
import R1Z.PV_W_R_MaskMaterial
import R1Z.PV_W_R_MaskedWithAttempt
import R1Z.PV_W_R_OpeningBatchBody
import R1Z.PV_W_R_OpeningInactiveBody
import R1Z.PV_W_R_PreReservedReserve
import R1Z.PV_W_R_PrepareOpening
import R1Z.PV_W_R_PrivateSaltStep
import R1Z.PV_W_R_PrivateSalts
import R1Z.PV_W_R_PrivateSaltsBody
import R1Z.PV_W_R_PublishCompact
import R1Z.PV_W_R_ReservationPath
import R1Z.PV_W_R_ReserveBuild
import R1Z.PV_W_R_ReserveFallible
import R1Z.PV_W_R_SyncDirectory
import R1Z.PV_W_R_ZeroFactor
import R1Z.PV_W_ReachedEffects
import R1Z.PV_W_ReachedThreading
import R1Z.PV_W_RecursiveLaws
import R1Z.PV_W_ReservationPath
import R1Z.PV_W_ReserveBuild
import R1Z.PV_W_StructuredBinds
import R1Z.PV_W_ZeroizingBridge

#print axioms R1Z.PV_W_Callbacks.erase_hash
#print axioms R1Z.PV_W_Callbacks.erase_store
#print axioms R1Z.PV_W_Callbacks.erase_ite
#print axioms R1Z.PV_W_Callbacks.erase_if_congr
#print axioms R1Z.PV_W_EnrichedMemory.commit_allocator
#print axioms R1Z.PV_W_EnrichedMemory.commit_os
#print axioms R1Z.PV_W_EnrichedMemory.commit_filesystem
#print axioms R1Z.PV_W_EnrichedMemory.effect_os
#print axioms R1Z.PV_W_EnrichedMemory.effect_filesystem
#print axioms R1Z.PV_W_EnrichedMemory.effect_projected_trace
#print axioms R1Z.PV_W_EnrichedMemory.effect_allocator
#print axioms R1Z.PV_W_FromSemantics.erase_program
#print axioms R1Z.PV_W_IfLaws.erase_if_congr
#print axioms R1Z.PV_W_Loops.finite_exact
#print axioms R1Z.PV_W_Loops.fuel_valid
#print axioms R1Z.PV_W_Loops.execution_threaded
#print axioms R1Z.PV_W_Loops.source_loop
#print axioms R1Z.PV_W_MaskedWithAttempt.erase_program
#print axioms R1Z.PV_W_MemoryCombined.current_selector
#print axioms R1Z.PV_W_MemoryLift.state_valid
#print axioms R1Z.PV_W_MemoryLift.state_bind
#print axioms R1Z.PV_W_MemoryLift.drop_source
#print axioms R1Z.PV_W_MemoryLift.drop_world
#print axioms R1Z.PV_W_MemoryLift.reserve_source
#print axioms R1Z.PV_W_MemoryLift.reserve_world
#print axioms R1Z.PV_W_MemoryLift.zero_source
#print axioms R1Z.PV_W_MemoryLift.zero_world
#print axioms R1Z.PV_W_Ownership.take_source
#print axioms R1Z.PV_W_Ownership.take_empty
#print axioms R1Z.PV_W_Ownership.take_other
#print axioms R1Z.PV_W_Ownership.take_twice
#print axioms R1Z.PV_W_Ownership.take_unique
#print axioms R1Z.PV_W_Ownership.drop_slot_empty
#print axioms R1Z.PV_W_Ownership.drop_slot_once
#print axioms R1Z.PV_W_Ownership.drop_slot_unique
#print axioms R1Z.PV_W_PrivateSalts.erase_program
#print axioms R1Z.PV_W_PrivateSaltsLoop.body_source
#print axioms R1Z.PV_W_PrivateSaltsLoop.source_loop_function
#print axioms R1Z.PV_W_PrivateSaltsLoop.finite_source
#print axioms R1Z.PV_W_PrivateSaltsLoop.finite_world
#print axioms R1Z.PV_W_PrivateSaltsLoop.world_threaded
#print axioms R1Z.PV_W_R_ApplyMaterial.erase_program
#print axioms R1Z.PV_W_R_AuditMasks.erase_program
#print axioms R1Z.PV_W_R_AuditMasksBody0.erase_program
#print axioms R1Z.PV_W_R_AuditMasksBody1.erase_program
#print axioms R1Z.PV_W_R_DurableReserve.erase_program
#print axioms R1Z.PV_W_R_DurableReserve.store_source
#print axioms R1Z.PV_W_R_Entry.erase_program
#print axioms R1Z.PV_W_R_FinishOpening.erase_program
#print axioms R1Z.PV_W_R_FixedColumn.erase_program
#print axioms R1Z.PV_W_R_FromSemantics.erase_program
#print axioms R1Z.PV_W_R_HostBuild.erase_program
#print axioms R1Z.PV_W_R_InactiveSumBody.erase_program
#print axioms R1Z.PV_W_R_MaskMaterial.erase_program
#print axioms R1Z.PV_W_R_MaskedWithAttempt.erase_program
#print axioms R1Z.PV_W_R_OpeningBatchBody.erase_program
#print axioms R1Z.PV_W_R_OpeningInactiveBody.erase_program
#print axioms R1Z.PV_W_R_PreReservedReserve.erase_program
#print axioms R1Z.PV_W_R_PreReservedReserve.store_source
#print axioms R1Z.PV_W_R_PrepareOpening.erase_program
#print axioms R1Z.PV_W_R_PrivateSaltStep.erase_program
#print axioms R1Z.PV_W_R_PrivateSalts.erase_program
#print axioms R1Z.PV_W_R_PrivateSaltsBody.erase_program
#print axioms R1Z.PV_W_R_PublishCompact.erase_program
#print axioms R1Z.PV_W_R_ReservationPath.erase_program
#print axioms R1Z.PV_W_R_ReserveBuild.erase_program
#print axioms R1Z.PV_W_R_ReserveFallible.erase_program
#print axioms R1Z.PV_W_R_SyncDirectory.erase_program
#print axioms R1Z.PV_W_R_ZeroFactor.erase_program
#print axioms R1Z.PV_W_ReachedEffects.erase_bind
#print axioms R1Z.PV_W_ReachedEffects.erase_perform
#print axioms R1Z.PV_W_ReachedEffects.erase_invoke
#print axioms R1Z.PV_W_ReachedEffects.erase_pure
#print axioms R1Z.PV_W_ReachedThreading.primitive_valid
#print axioms R1Z.PV_W_ReachedThreading.entry_source
#print axioms R1Z.PV_W_ReachedThreading.entry_threaded
#print axioms R1Z.PV_W_ReachedThreading.entry_operational
#print axioms R1Z.PV_W_ReachedThreading.project_run
#print axioms R1Z.PV_W_RecursiveLaws.erase_ite
#print axioms R1Z.PV_W_RecursiveLaws.bind_congr
#print axioms R1Z.PV_W_RecursiveLaws.eval_expand
#print axioms R1Z.PV_W_ReservationPath.erase_program
#print axioms R1Z.PV_W_ReserveBuild.erase_program
#print axioms R1Z.PV_W_StructuredBinds.erase_join
#print axioms R1Z.PV_W_ZeroizingBridge.wrapper_value
#print axioms R1Z.PV_W_ZeroizingBridge.wrapper_outcome
#print axioms R1Z.PV_W_ZeroizingBridge.explicit_then_drop_counts
#print axioms R1Z.PV_W_ZeroizingBridge.drop_consumed_source
#print axioms R1Z.PV_W_Enriched.project_threaded
