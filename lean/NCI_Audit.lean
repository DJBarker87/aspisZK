import NCI_ArrayFrame
import NCI_BasisBounds
import NCI_BasisModelStep
import NCI_FieldLog
import NCI_FinishCanonical
import NCI_GetterModel
import NCI_InspectMk
import NCI_InspectPrimitives
import NCI_InspectReader
import NCI_KMXFrames
import NCI_NextBound
import NCI_PendingReducer
import NCI_PendingValue
import NCI_Persistence
import NCI_QueryInvariant
import NCI_ReaderLayout
import NCI_ReaderWindows
import NCI_ResidueBounds
import NCI_ResidueInvariant
import NCI_ResidueWords
import NCI_ResumeDomains
import NCI_SectionCursor
import NCI_WideDomains
import NCI_WindowFrame

#print axioms AspisR1.NCI_ArrayFrame.write
#print axioms AspisR1.NCI_BasisBounds.stage_half
#print axioms AspisR1.NCI_BasisBounds.write_domain
#print axioms AspisR1.NCI_BasisBounds.doubled
#print axioms AspisR1.NCI_BasisBounds.active_stage
#print axioms AspisR1.NCI_BasisBounds.terms_advance
#print axioms AspisR1.NCI_BasisBounds.flushes
#print axioms AspisR1.NCI_BasisModelStep.source_step
#print axioms AspisR1.NCI_BasisModelStep.index_value
#print axioms AspisR1.NCI_BasisModelStep.read_exists
#print axioms AspisR1.NCI_FieldLog.instantiate
#print axioms AspisR1.NCI_FinishCanonical.prefix_length
#print axioms AspisR1.NCI_FinishCanonical.finish_domains
#print axioms AspisR1.NCI_GetterModel.array_get
#print axioms AspisR1.NCI_GetterModel.slice_get
#print axioms AspisR1.NCI_KMXFrames.window
#print axioms AspisR1.NCI_KMXFrames.checkpoint_weights
#print axioms AspisR1.NCI_KMXFrames.checkpoint_frame
#print axioms AspisR1.NCI_KMXFrames.disjoint
#print axioms AspisR1.NCI_NextBound.guard
#print axioms AspisR1.NCI_NextBound.successful_header
#print axioms AspisR1.NCI_NextBound.successful_next
#print axioms AspisR1.NCI_PendingReducer.primitive_eq
#print axioms AspisR1.NCI_PendingReducer.reducer_ok
#print axioms AspisR1.NCI_PendingValue.successful_value
#print axioms AspisR1.NCI_Persistence.saved_loaded
#print axioms AspisR1.NCI_QueryInvariant.accepted_head
#print axioms AspisR1.NCI_QueryInvariant.accepted_bounds
#print axioms AspisR1.NCI_QueryInvariant.accepted_fresh
#print axioms AspisR1.NCI_QueryInvariant.accepted_unique
#print axioms AspisR1.NCI_ReaderLayout.body_end
#print axioms AspisR1.NCI_ReaderLayout.checksum_end
#print axioms AspisR1.NCI_ReaderLayout.weight_read_bound
#print axioms AspisR1.NCI_ReaderLayout.semantic_read_bound
#print axioms AspisR1.NCI_ReaderLayout.query_read_bound
#print axioms AspisR1.NCI_ReaderLayout.bounded_raw
#print axioms AspisR1.NCI_ReaderWindows.weight_step
#print axioms AspisR1.NCI_ReaderWindows.semantic_step
#print axioms AspisR1.NCI_ResidueBounds.product_bound
#print axioms AspisR1.NCI_ResidueBounds.group_nowrap
#print axioms AspisR1.NCI_ResidueBounds.next_partial
#print axioms AspisR1.NCI_ResidueBounds.fold_boundary
#print axioms AspisR1.NCI_ResidueBounds.flush_schedule
#print axioms AspisR1.NCI_ResidueBounds.twelve_queries
#print axioms AspisR1.NCI_ResidueInvariant.fold_mod
#print axioms AspisR1.NCI_ResidueInvariant.step_mod
#print axioms AspisR1.NCI_ResidueInvariant.step_valid
#print axioms AspisR1.NCI_ResidueInvariant.run_valid
#print axioms AspisR1.NCI_ResidueInvariant.run_mod
#print axioms AspisR1.NCI_ResidueWords.word_exists
#print axioms AspisR1.NCI_ResidueWords.product_sum
#print axioms AspisR1.NCI_ResumeDomains.sourceK_canonical
#print axioms AspisR1.NCI_ResumeDomains.returned_domains
#print axioms AspisR1.NCI_SectionCursor.successful_section
#print axioms AspisR1.NCI_WideDomains.sourceE_canonical
#print axioms AspisR1.NCI_WideDomains.e_at
#print axioms AspisR1.NCI_WideDomains.k_at
#print axioms AspisR1.NCI_WideDomains.resumed_wide
#print axioms AspisR1.NCI_WideDomains.resumed_coordinates
#print axioms AspisR1.NCI_WindowFrame.cell
#print axioms AspisR1.NCI_WindowFrame.after
