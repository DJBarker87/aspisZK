import SCJ_AccountProjection
import SCJ_AlignedEvent
import SCJ_Alignment
import SCJ_BeforeTable
import SCJ_Checkpoint
import SCJ_Composition
import SCJ_Domination
import SCJ_EventTransport
import SCJ_FirstHitWitness
import SCJ_FirstRead
import SCJ_NativeLoaded
import SCJ_Nonvacuity
import SCJ_OrderObstruction
import SCJ_OrderedTransport
import SCJ_Projection
import SCJ_TableExtension
import SCJ_Top
import Rc8_Top
import Rc8_Nonvacuity
import SCG_Nonvacuity
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 160
#print axioms AspisR1.SCJ_AccountProjection.event_implies
#print axioms AspisR1.SCJ_AlignedEvent.hits
#print axioms AspisR1.SCJ_Alignment.sublist
#print axioms AspisR1.SCJ_BeforeTable.extension
#print axioms AspisR1.SCJ_Checkpoint.same_saved
#print axioms AspisR1.SCJ_Checkpoint.entry_saved
#print axioms AspisR1.SCJ_Composition.account_of_branch
#print axioms AspisR1.SCJ_Domination.indicator_obstruction
#print axioms AspisR1.SCJ_Domination.of_transport
#print axioms AspisR1.SCJ_Projection.event_implies_aligned
#print axioms AspisR1.SCJ_Projection.not_all_sublists_aligned
#print axioms AspisR1.SCJ_FirstHitWitness.witness
#print axioms AspisR1.SCJ_FirstRead.cached_interior
#print axioms AspisR1.SCJ_NativeLoaded.entry_loaded
#print axioms AspisR1.SCJ_NativeLoaded.ideal_cut
#print axioms AspisR1.SCJ_Nonvacuity.real_bytes
#print axioms AspisR1.SCJ_OrderObstruction.sublist_not_first_order
#print axioms AspisR1.SCJ_Projection.event_implies
#print axioms AspisR1.SCJ_Projection.event_implies_refuted
#print axioms AspisR1.SCJ_Projection.clean_transport_refuted
#print axioms AspisR1.SCJ_TableExtension.known
#print axioms AspisR1.SCJ_TableExtension.put
#print axioms AspisR1.SCJ_TableExtension.bad
#print axioms AspisR1.SCJ_Top.unrestricted_runtime_obstruction
#print axioms AspisR1.Rc8_Top.deployed
#print axioms AspisR1.Rc8_Nonvacuity.composed
#print axioms AspisR1.SCG_Nonvacuity.joint
#check @AspisR1.Rc8_Top.deployed
#check @AspisR1.SCJ_NativeLoaded.ideal_cut
#check @AspisR1.SCJ_Projection.event_implies
#check @AspisR1.SCJ_AccountProjection.event_implies
#check @AspisR1.SCJ_Composition.account_of_branch
#print AspisR1.SCJ_Alignment.Aligned
