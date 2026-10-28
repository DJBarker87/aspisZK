import PV_L2D_AuditSampler
import PV_L2D_BaseEmbedding
import PV_L2D_CtZero
import PV_L2D_IndexedTail
import PV_L2D_MerkleCost
import PV_L2D_MerkleGeometry
import PV_L2D_MerkleGroups
import PV_L2D_MerkleOrdered
import PV_L2D_MerklePlan
import PV_L2D_MerkleSafe
import PV_L2D_PublicationCaps
import PV_L2D_PublicationIndices
import PV_L2D_PublicationTrace
import PV_L2D_Qm31Embedding
import PV_L2D_QueryBounds
import PV_L2D_QueryDriver
import PV_L2D_QueryGuards
import PV_L2D_QueryScan
import PV_L2D_SlotCaps
import PV_L2D_TreeShape
import PV_L2D_ZeroTail
set_option autoImplicit false
/- Scoped helper audit only; no endpoint row premise is discharged. -/
#print axioms PV_L2D_BaseEmbedding.word_zero
#print axioms PV_L2D_BaseEmbedding.canonical_base
#print axioms PV_L2D_BaseEmbedding.embed_base
#print axioms PV_L2D_BaseEmbedding.lower_zero_tail
#print axioms PV_L2D_CtZero.subtract_zero
#print axioms PV_L2D_CtZero.reduce_zero
#print axioms PV_L2D_IndexedTail.complete
#print axioms PV_L2D_IndexedTail.array_eight
#print axioms PV_L2D_IndexedTail.honest_eight
#print axioms PV_L2D_MerkleCost.partition
#print axioms PV_L2D_MerkleCost.binary_branch
#print axioms PV_L2D_MerkleCost.cost_step
#print axioms PV_L2D_MerkleCost.plan_cost
#print axioms PV_L2D_MerkleCost.ordinary_cap
#print axioms PV_L2D_MerkleCost.folded_cap
#print axioms PV_L2D_MerkleGeometry.level_bound
#print axioms PV_L2D_MerkleGeometry.levels_bound
#print axioms PV_L2D_MerkleGeometry.levels_ordered
#print axioms PV_L2D_MerkleGeometry.interval_count
#print axioms PV_L2D_MerkleGeometry.occupancy_domain
#print axioms PV_L2D_MerkleGeometry.occupancy_initial
#print axioms PV_L2D_MerkleGeometry.levels_shift
#print axioms PV_L2D_MerkleGroups.paired_iff
#print axioms PV_L2D_MerkleGroups.group_test
#print axioms PV_L2D_MerkleGroups.counted_equals_emitted
#print axioms PV_L2D_MerkleOrdered.tail_mem
#print axioms PV_L2D_MerkleOrdered.parent_mem
#print axioms PV_L2D_MerkleOrdered.no_pair_lower
#print axioms PV_L2D_MerkleOrdered.ordered
#print axioms PV_L2D_MerkleOrdered.counted_plan
#print axioms PV_L2D_MerklePlan.erase_payload
#print axioms PV_L2D_MerklePlan.emitted_length
#print axioms PV_L2D_MerklePlan.complete_read_law
#print axioms PV_L2D_MerklePlan.sibling_bound
#print axioms PV_L2D_MerklePlan.parent_bound
#print axioms PV_L2D_MerklePlan.level_parent_count
#print axioms PV_L2D_MerklePlan.level_sibling_count
#print axioms PV_L2D_MerklePlan.plan_bound
#print axioms PV_L2D_MerklePlan.binary_native_slot_bound
#print axioms PV_L2D_MerklePlan.shared_pair
#print axioms PV_L2D_MerkleSafe.sibling_mem
#print axioms PV_L2D_MerkleSafe.addresses_safe
#print axioms PV_L2D_MerkleSafe.eighteen
#print axioms PV_L2D_PublicationCaps.member_source
#print axioms PV_L2D_PublicationCaps.ordinary_domain
#print axioms PV_L2D_PublicationCaps.folded_domain
#print axioms PV_L2D_PublicationCaps.all_slots
#print axioms PV_L2D_PublicationCaps.fixed_padding
#print axioms PV_L2D_PublicationIndices.seek_bound
#print axioms PV_L2D_PublicationIndices.source_insert
#print axioms PV_L2D_PublicationIndices.insert_length
#print axioms PV_L2D_PublicationIndices.insert_mem
#print axioms PV_L2D_PublicationIndices.insert_ordered
#print axioms PV_L2D_PublicationIndices.build_length
#print axioms PV_L2D_PublicationIndices.build_ordered
#print axioms PV_L2D_PublicationIndices.build_mem
#print axioms PV_L2D_PublicationIndices.publication_length
#print axioms PV_L2D_PublicationIndices.publication_ordered
#print axioms PV_L2D_PublicationTrace.erases
#print axioms PV_L2D_PublicationTrace.full_replay
#print axioms PV_L2D_PublicationTrace.empty_trace
#print axioms PV_L2D_PublicationTrace.query_set_insufficient
#print axioms PV_L2D_PublicationTrace.source_insert_erases
#print axioms PV_L2D_Qm31Embedding.remainder_total
#print axioms PV_L2D_Qm31Embedding.word_total
#print axioms PV_L2D_Qm31Embedding.canonical_total
#print axioms PV_L2D_Qm31Embedding.embed_total
#print axioms PV_L2D_Qm31Embedding.from_qm31_exact
#print axioms PV_L2D_Qm31Embedding.upper_zero
#print axioms PV_L2D_Qm31Embedding.upper_limb_tail
#print axioms PV_L2D_Qm31Embedding.frozen_upper_limb_tail
#print axioms PV_L2D_QueryBounds.initial
#print axioms PV_L2D_QueryBounds.next_admitted
#print axioms PV_L2D_QueryBounds.scan_admitted
#print axioms PV_L2D_QueryBounds.member_read_safe
#print axioms PV_L2D_QueryBounds.write_safe
#print axioms PV_L2D_QueryBounds.masked_bound
#print axioms PV_L2D_QueryDriver.scan_count
#print axioms PV_L2D_QueryDriver.drive_admitted
#print axioms PV_L2D_QueryDriver.success_shape
#print axioms PV_L2D_QueryDriver.selected_range
#print axioms PV_L2D_QueryDriver.block_boundary
#print axioms PV_L2D_QueryDriver.empty_exhaustion
#print axioms PV_L2D_QueryGuards.core_value
#print axioms PV_L2D_QueryGuards.host_value
#print axioms PV_L2D_QueryGuards.traces_differ
#print axioms PV_L2D_QueryGuards.expand_exact
#print axioms PV_L2D_QueryGuards.cap_both
#print axioms PV_L2D_QueryScan.member_value
#print axioms PV_L2D_QueryScan.complete
#print axioms PV_L2D_QueryScan.no_empty_guard
#print axioms PV_L2D_QueryScan.exact_stop
#print axioms PV_L2D_QueryScan.boundary
#print axioms PV_L2D_QueryScan.duplicate_history_matters
#print axioms PV_L2D_QueryScan.complete_replay
#print axioms PV_L2D_SlotCaps.telescope
#print axioms PV_L2D_SlotCaps.bottom
#print axioms PV_L2D_SlotCaps.ordinary
#print axioms PV_L2D_SlotCaps.folded
#print axioms PV_L2D_SlotCaps.exact_caps
#print axioms PV_L2D_SlotCaps.padding_length
#print axioms PV_L2D_TreeShape.parent_length
#print axioms PV_L2D_TreeShape.level_count
#print axioms PV_L2D_TreeShape.level_shape
#print axioms PV_L2D_TreeShape.root_exists
#print axioms PV_L2D_TreeShape.planned_read
#print axioms PV_L2D_ZeroTail.complete_zero
#print axioms PV_L2D_ZeroTail.complete_passing
#print axioms PV_L2D_ZeroTail.first_bad
#print axioms PV_L2D_ZeroTail.ok_iff
#print axioms PV_L2D_ZeroTail.honest_trace
#print axioms PV_L2D_ZeroTail.lower_limbs_irrelevant
#print axioms PV_L2D_ZeroTail.base_honest
#print axioms PV_L2D_ZeroTail.secure_honest
#print axioms PV_L2D_ZeroTail.nonvacuous
