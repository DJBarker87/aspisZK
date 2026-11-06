import NKH_COMBINED_IMPORT
import NKL_CanonicalChildren
import NKL_CanonicalConcat
import NKL_CanonicalInstallation
import NKL_CanonicalK
import NKL_CanonicalKCarrier
import NKL_CanonicalWindows
import NKL_Checks
import NKL_ChildCanonical
import NKL_ChunkCanonical
import NKL_ClosedChildren
import NKL_ExitTransport
import NKL_ExplicitBody
import NKL_LeafTotal
import NKL_NativeGuard
import NKL_OpeningCanonical
import NKL_OpeningSlots
import NKL_PrefixCanonical
import NKL_ReadWindows
import NKL_ScanAtoms
import NKL_ScanDomains
import NKL_ScanModel
import NKL_ScanRoot
import NKL_ScanRows
import NKL_ScanSequence
import NKL_StepErasure
import NKL_TailGeometry
import NKL_VerifyCut
import NKL_WordCanonical

set_option pp.proofs false
#print AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.RPx_Deployed.deployed
#print NKL_CanonicalChildren.compact_result
#print axioms NKL_CanonicalChildren.compact_result
#print NKL_CanonicalChildren.echeck_result
#print axioms NKL_CanonicalChildren.echeck_result
#print NKL_CanonicalChildren.compact_call
#print axioms NKL_CanonicalChildren.compact_call
#print NKL_CanonicalChildren.echeck_call
#print axioms NKL_CanonicalChildren.echeck_call
#print NKL_CanonicalConcat.append
#print axioms NKL_CanonicalConcat.append
#print NKL_CanonicalConcat.partition
#print axioms NKL_CanonicalConcat.partition
#print NKL_CanonicalInstallation.k_total
#print axioms NKL_CanonicalInstallation.k_total
#print NKL_CanonicalInstallation.e_total
#print axioms NKL_CanonicalInstallation.e_total
#print NKL_CanonicalInstallation.cv_total
#print axioms NKL_CanonicalInstallation.cv_total
#print NKL_CanonicalInstallation.k_c1
#print axioms NKL_CanonicalInstallation.k_c1
#print NKL_CanonicalInstallation.k_c2
#print axioms NKL_CanonicalInstallation.k_c2
#print NKL_CanonicalInstallation.source
#print axioms NKL_CanonicalInstallation.source
#print NKL_CanonicalK.good_eq_guard
#print axioms NKL_CanonicalK.good_eq_guard
#print NKL_CanonicalK.word_value
#print axioms NKL_CanonicalK.word_value
#print NKL_CanonicalK.source
#print axioms NKL_CanonicalK.source
#print NKL_CanonicalK.native_result
#print axioms NKL_CanonicalK.native_result
#print NKL_CanonicalKCarrier.decoder
#print axioms NKL_CanonicalKCarrier.decoder
#print NKL_CanonicalKCarrier.selected_tag
#print axioms NKL_CanonicalKCarrier.selected_tag
#print NKL_CanonicalWindows.nested
#print axioms NKL_CanonicalWindows.nested
#print NKL_CanonicalWindows.length
#print axioms NKL_CanonicalWindows.length
#print NKL_CanonicalWindows.canonical_window
#print axioms NKL_CanonicalWindows.canonical_window
#print NKL_CanonicalWindows.index
#print axioms NKL_CanonicalWindows.index
#print NKL_CanonicalWindows.allFrom
#print axioms NKL_CanonicalWindows.allFrom
#print NKL_CanonicalWindows.selected
#print axioms NKL_CanonicalWindows.selected
#print NKL_Checks.slot_length
#print axioms NKL_Checks.slot_length
#print NKL_Checks.opening_length
#print axioms NKL_Checks.opening_length
#print NKL_Checks.row_length
#print axioms NKL_Checks.row_length
#print NKL_Checks.allFrom
#print axioms NKL_Checks.allFrom
#print NKL_Checks.slot_test
#print axioms NKL_Checks.slot_test
#print NKL_Checks.opening_test
#print axioms NKL_Checks.opening_test
#print NKL_Checks.row_test
#print axioms NKL_Checks.row_test
#print NKL_Checks.prefix_test
#print axioms NKL_Checks.prefix_test
#print NKL_Checks.source
#print axioms NKL_Checks.source
#print NKL_ChildCanonical.compact
#print axioms NKL_ChildCanonical.compact
#print NKL_ChildCanonical.echeck
#print axioms NKL_ChildCanonical.echeck
#print NKL_ChildCanonical.compact_decide
#print axioms NKL_ChildCanonical.compact_decide
#print NKL_ChildCanonical.echeck_decide
#print axioms NKL_ChildCanonical.echeck_decide
#print NKL_ChunkCanonical.le32
#print axioms NKL_ChunkCanonical.le32
#print NKL_ChunkCanonical.window
#print axioms NKL_ChunkCanonical.window
#print NKL_ChunkCanonical.chunk
#print axioms NKL_ChunkCanonical.chunk
#print NKL_ChunkCanonical.blocks
#print axioms NKL_ChunkCanonical.blocks
#print NKL_ClosedChildren.scalar
#print axioms NKL_ClosedChildren.scalar
#print NKL_ClosedChildren.actualK
#print axioms NKL_ClosedChildren.actualK
#print NKL_ClosedChildren.quadratic
#print axioms NKL_ClosedChildren.quadratic
#print NKL_ClosedChildren.opening_reference
#print axioms NKL_ClosedChildren.opening_reference
#print NKL_ClosedChildren.opening
#print axioms NKL_ClosedChildren.opening
#print NKL_ExitTransport.parse_cut
#print axioms NKL_ExitTransport.parse_cut
#print NKL_ExitTransport.result
#print axioms NKL_ExitTransport.result
#print NKL_ExitTransport.observed
#print axioms NKL_ExitTransport.observed
#print NKL_ExitTransport.no_suffix
#print axioms NKL_ExitTransport.no_suffix
#print NKL_LeafTotal.total
#print axioms NKL_LeafTotal.total
#print NKL_LeafTotal.source
#print axioms NKL_LeafTotal.source
#print NKL_NativeGuard.k
#print axioms NKL_NativeGuard.k
#print NKL_NativeGuard.source
#print axioms NKL_NativeGuard.source
#print NKL_OpeningCanonical.source
#print axioms NKL_OpeningCanonical.source
#print NKL_OpeningCanonical.value
#print axioms NKL_OpeningCanonical.value
#print NKL_OpeningSlots.scalars
#print axioms NKL_OpeningSlots.scalars
#print NKL_OpeningSlots.slot
#print axioms NKL_OpeningSlots.slot
#print NKL_OpeningSlots.all_slots
#print axioms NKL_OpeningSlots.all_slots
#print NKL_OpeningSlots.cover
#print axioms NKL_OpeningSlots.cover
#print NKL_PrefixCanonical.slice_join
#print axioms NKL_PrefixCanonical.slice_join
#print NKL_PrefixCanonical.source
#print axioms NKL_PrefixCanonical.source
#print NKL_ReadWindows.scalar_bytes
#print axioms NKL_ReadWindows.scalar_bytes
#print NKL_ReadWindows.c1_bytes
#print axioms NKL_ReadWindows.c1_bytes
#print NKL_ReadWindows.c2_bytes
#print axioms NKL_ReadWindows.c2_bytes
#print NKL_ReadWindows.scalar
#print axioms NKL_ReadWindows.scalar
#print NKL_ReadWindows.c1
#print axioms NKL_ReadWindows.c1
#print NKL_ReadWindows.c2
#print axioms NKL_ReadWindows.c2
#print NKL_ScanAtoms.k
#print axioms NKL_ScanAtoms.k
#print NKL_ScanAtoms.source
#print axioms NKL_ScanAtoms.source
#print NKL_ScanAtoms.accepted_test
#print axioms NKL_ScanAtoms.accepted_test
#print NKL_ScanDomains.slot
#print axioms NKL_ScanDomains.slot
#print NKL_ScanDomains.opening
#print axioms NKL_ScanDomains.opening
#print NKL_ScanDomains.row
#print axioms NKL_ScanDomains.row
#print NKL_ScanDomains.header
#print axioms NKL_ScanDomains.header
#print NKL_ScanDomains.source
#print axioms NKL_ScanDomains.source
#print NKL_ScanModel.predicate
#print axioms NKL_ScanModel.predicate
#print NKL_ScanModel.value
#print axioms NKL_ScanModel.value
#print NKL_ScanModel.source
#print axioms NKL_ScanModel.source
#print NKL_ScanModel.adopted
#print axioms NKL_ScanModel.adopted
#print NKL_ScanRoot.all_source
#print axioms NKL_ScanRoot.all_source
#print NKL_ScanRoot.deployed
#print axioms NKL_ScanRoot.deployed
#print NKL_ScanRoot.adopted
#print axioms NKL_ScanRoot.adopted
#print NKL_ScanRoot.no_later_event
#print axioms NKL_ScanRoot.no_later_event
#print NKL_ScanRoot.success_events
#print axioms NKL_ScanRoot.success_events
#print NKL_ScanRows.one
#print axioms NKL_ScanRows.one
#print NKL_ScanRows.source
#print axioms NKL_ScanRows.source
#print NKL_ScanSequence.exact
#print axioms NKL_ScanSequence.exact
#print NKL_ScanSequence.result
#print axioms NKL_ScanSequence.result
#print NKL_ScanSequence.trace_prefix
#print axioms NKL_ScanSequence.trace_prefix
#print NKL_ScanSequence.success_trace
#print axioms NKL_ScanSequence.success_trace
#print NKL_ScanSequence.rejection_trace
#print axioms NKL_ScanSequence.rejection_trace
#print NKL_StepErasure.map_ok
#print axioms NKL_StepErasure.map_ok
#print NKL_StepErasure.map_bind
#print axioms NKL_StepErasure.map_bind
#print NKL_StepErasure.map_ite
#print axioms NKL_StepErasure.map_ite
#print NKL_StepErasure.map_pair
#print axioms NKL_StepErasure.map_pair
#print NKL_StepErasure.map_cf
#print axioms NKL_StepErasure.map_cf
#print NKL_StepErasure.source
#print axioms NKL_StepErasure.source
#print NKL_TailGeometry.cap_bound
#print axioms NKL_TailGeometry.cap_bound
#print NKL_TailGeometry.counted_prefix
#print axioms NKL_TailGeometry.counted_prefix
#print NKL_TailGeometry.suffix
#print axioms NKL_TailGeometry.suffix
#print NKL_TailGeometry.tx2_bytes
#print axioms NKL_TailGeometry.tx2_bytes
#print NKL_VerifyCut.result
#print axioms NKL_VerifyCut.result
#print NKL_VerifyCut.indices
#print axioms NKL_VerifyCut.indices
#print NKL_VerifyCut.values
#print axioms NKL_VerifyCut.values
#print NKL_WordCanonical.one
#print axioms NKL_WordCanonical.one
#print NKL_WordCanonical.scalar_bytes
#print axioms NKL_WordCanonical.scalar_bytes
#print NKL_WordCanonical.scalar
#print axioms NKL_WordCanonical.scalar
#print NKL_WordCanonical.limb_bytes
#print axioms NKL_WordCanonical.limb_bytes
#print NKL_WordCanonical.k_word
#print axioms NKL_WordCanonical.k_word
#print NKL_WordCanonical.k
#print axioms NKL_WordCanonical.k
