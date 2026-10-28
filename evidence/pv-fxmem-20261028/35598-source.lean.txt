import R1Z.PV_FXM_DropCounterexample
import R1Z.PV_FXM_DropWorld
import R1Z.PV_FXM_DropSelected
import R1Z.PV_FXM_ZeroWorld
import R1Z.PV_FXM_ZeroTrace
import R1Z.PV_FXM_ZeroSelected
import R1Z.PV_FXM_ZeroDrop
import R1Z.PV_FXM_ZeroConsumed
import R1Z.PV_FXM_ReserveWorld
import R1Z.PV_FXM_ReserveFacts
import R1Z.PV_FXM_ReserveLayout
import R1Z.PV_FXM_ReservePrimitive
import R1Z.PV_FXM_ReserveSelected
import R1Z.PV_FXM_ReserveCaller
import R1Z.PV_FXM_Physical
import R1Z.PV_FXM_AuditInstall

-- One combined axiom audit; statement scope is documented in AUDIT.md.
#print axioms R1Z.PV_FXM_DropCounterexample.no_world_free_callback
#print axioms R1Z.PV_FXM_DropCounterexample.result_distinct
#print axioms R1Z.PV_FXM_DropCounterexample.witness
#print axioms R1Z.PV_FXM_DropCounterexample.no_uniform_projection
#print axioms R1Z.PV_FXM_DropCounterexample.state_indexed_nonvacuous
#print axioms R1Z.PV_FXM_DropWorld.source_reference
#print axioms R1Z.PV_FXM_DropWorld.effects
#print axioms R1Z.PV_FXM_DropWorld.no_capacity
#print axioms R1Z.PV_FXM_DropWorld.allocated
#print axioms R1Z.PV_FXM_DropWorld.caller_composition
#print axioms R1Z.PV_FXM_DropWorld.nonvacuous
#print axioms R1Z.PV_FXM_DropSelected.installed
#print axioms R1Z.PV_FXM_DropSelected.other_types
#print axioms R1Z.PV_FXM_DropSelected.other_fields
#print axioms R1Z.PV_FXM_DropSelected.projection
#print axioms R1Z.PV_FXM_DropSelected.execution
#print axioms R1Z.PV_FXM_ZeroWorld.source_reference
#print axioms R1Z.PV_FXM_ZeroWorld.counts
#print axioms R1Z.PV_FXM_ZeroWorld.frame
#print axioms R1Z.PV_FXM_ZeroWorld.outside
#print axioms R1Z.PV_FXM_ZeroWorld.overwritten
#print axioms R1Z.PV_FXM_ZeroWorld.caller_composition
#print axioms R1Z.PV_FXM_ZeroTrace.history
#print axioms R1Z.PV_FXM_ZeroTrace.trace_length
#print axioms R1Z.PV_FXM_ZeroTrace.writes_recorded
#print axioms R1Z.PV_FXM_ZeroTrace.nonvacuous
#print axioms R1Z.PV_FXM_ZeroSelected.byte_step
#print axioms R1Z.PV_FXM_ZeroSelected.scalar_execution
#print axioms R1Z.PV_FXM_ZeroSelected.byte_value
#print axioms R1Z.PV_FXM_ZeroSelected.elements_value
#print axioms R1Z.PV_FXM_ZeroSelected.array_value
#print axioms R1Z.PV_FXM_ZeroSelected.scalar_installed
#print axioms R1Z.PV_FXM_ZeroSelected.array_installed
#print axioms R1Z.PV_FXM_ZeroSelected.other_fields
#print axioms R1Z.PV_FXM_ZeroSelected.execution
#print axioms R1Z.PV_FXM_ZeroConsumed.emitted_default
#print axioms R1Z.PV_FXM_ZeroConsumed.emitted_scalar
#print axioms R1Z.PV_FXM_ZeroConsumed.emitted_array
#print axioms R1Z.PV_FXM_ZeroConsumed.emitted_execution
#print axioms R1Z.PV_FXM_ReserveWorld.usize_exact
#print axioms R1Z.PV_FXM_ReserveWorld.source_reference
#print axioms R1Z.PV_FXM_ReserveWorld.values_preserved
#print axioms R1Z.PV_FXM_ReserveWorld.no_growth
#print axioms R1Z.PV_FXM_ReserveWorld.allocation_error
#print axioms R1Z.PV_FXM_ReserveWorld.success_capacity
#print axioms R1Z.PV_FXM_ReserveWorld.caller_composition
#print axioms R1Z.PV_FXM_ReserveFacts.finish_effects
#print axioms R1Z.PV_FXM_ReserveFacts.overflow_world
#print axioms R1Z.PV_FXM_ReserveFacts.copied_prefix
#print axioms R1Z.PV_FXM_ReserveFacts.outside_memory
#print axioms R1Z.PV_FXM_ReserveFacts.new_spare_uninitialized
#print axioms R1Z.PV_FXM_ReserveFacts.buffer_nonvacuous
#print axioms R1Z.PV_FXM_ReserveLayout.product_error
#print axioms R1Z.PV_FXM_ReserveLayout.wrapped_available
#print axioms R1Z.PV_FXM_ReserveLayout.aligned_limit
#print axioms R1Z.PV_FXM_ReserveLayout.same_alignment
#print axioms R1Z.PV_FXM_ReservePrimitive.allocate_branch
#print axioms R1Z.PV_FXM_ReservePrimitive.allocate_address_irrelevant
#print axioms R1Z.PV_FXM_ReservePrimitive.realloc_branch
#print axioms R1Z.PV_FXM_ReservePrimitive.exact_size
#print axioms R1Z.PV_FXM_ReservePrimitive.alignment
#print axioms R1Z.PV_FXM_ReserveSelected.other_fields
#print axioms R1Z.PV_FXM_ReserveSelected.error_payload
#print axioms R1Z.PV_FXM_ReserveSelected.complete
#print axioms R1Z.PV_FXM_ReserveSelected.execution
#print axioms R1Z.PV_FXM_ReserveCaller.execution
#print axioms R1Z.PV_FXM_ReserveCaller.metadata_header
#print axioms R1Z.PV_FXM_Physical.drop_effect
#print axioms R1Z.PV_FXM_Physical.drop_source_reference
#print axioms R1Z.PV_FXM_Physical.reserve_effect
#print axioms R1Z.PV_FXM_Physical.reserve_source_reference
#print axioms R1Z.PV_FXM_AuditInstall.other_fields
#print axioms R1Z.PV_FXM_AuditInstall.drop
#print axioms R1Z.PV_FXM_AuditInstall.other_drop_types
#print axioms R1Z.PV_FXM_AuditInstall.array
#print axioms R1Z.PV_FXM_AuditInstall.scalar
#print axioms R1Z.PV_FXM_AuditInstall.reserve

#print axioms R1Z.PV_FXM_ZeroDrop.complete
#print axioms R1Z.PV_FXM_ZeroDrop.caller_composition
