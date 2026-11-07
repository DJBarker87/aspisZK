import LIB_Transcribed
import LIB_Readonly
import LIB_Zero
import LIB_Distinct
import LIB_CheckpointReuse
import LIB_RegistryPredicates
import LIB_Key
import LIB_Observer
import LIB_Route
import LIB_BoxReference
import LIB_Snapshot
import LIB_DigestCanonical
import LIB_ErrorDebug
set_option autoImplicit false
namespace LIB_TranscribedAll
/-- Concrete helper models and their emitted-copy/native source associations.
These are support exports; library bundles and principal consumption follow. -/
abbrev data := @LIB_Transcribed.data
abbrev data_len := @LIB_CheckpointReuse.length
abbrev key := @LIB_Key.result
abbrev readonlyBuffer := @LIB_Readonly.buffer
abbrev readonlyAccount := @LIB_Readonly.owned
abbrev verifierCheckpoint := @LIB_CheckpointReuse.packet
abbrev distinct3 := @LIB_Distinct.three
abbrev distinct7 := @LIB_Distinct.seven
abbrev zero := @LIB_Zero.result
abbrev snapshot := @LIB_Snapshot.law
abbrev snapshot_source := @LIB_Snapshot.source
abbrev active1 := @LIB_RegistryPredicates.active1
abbrev active2 := @LIB_RegistryPredicates.active2
abbrev paused1 := @LIB_RegistryPredicates.paused1
abbrev paused2 := @LIB_RegistryPredicates.paused2
abbrev immutable1 := @LIB_RegistryPredicates.immutable1
abbrev immutable2 := @LIB_RegistryPredicates.immutable2
abbrev boxed := @LIB_BoxReference.member
abbrev master_box_source := @LIB_BoxReference.master_source
abbrev checkpoint_box_source := @LIB_BoxReference.checkpoint_source
abbrev stage1Route := @LIB_RouteCarrier.stage1_iff
abbrev asq8Route := @LIB_RouteCarrier.asq8_iff
abbrev admitted := @LIB_Route.entry_emitted
abbrev digest := @LIB_DigestCanonical.source
abbrev error := @LIB_ErrorDebug.native_source
abbrev mapVErr := @NMS_R2ErrorSource.full
abbrev observer := @LIB_Observer.emitted
abbrev mark := @LIB_Mark.effects
#print axioms data
#print axioms data_len
#print axioms key
#print axioms readonlyBuffer
#print axioms readonlyAccount
#print axioms verifierCheckpoint
#print axioms distinct3
#print axioms distinct7
#print axioms zero
#print axioms snapshot
#print axioms snapshot_source
#print axioms active1
#print axioms active2
#print axioms paused1
#print axioms paused2
#print axioms immutable1
#print axioms immutable2
#print axioms boxed
#print axioms master_box_source
#print axioms checkpoint_box_source
#print axioms stage1Route
#print axioms asq8Route
#print axioms admitted
#print axioms digest
#print axioms error
#print axioms mapVErr
#print axioms observer
#print axioms mark
end LIB_TranscribedAll
