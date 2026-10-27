import R1Z.PV_OptB_AdmittedFamily
import R1Z.PV_OptB_AdmittedPoleDifference
import R1Z.PV_OptB_AdmittedTrace
import R1Z.PV_OptB_AffineTuple
import R1Z.PV_OptB_Cardinality
import R1Z.PV_OptB_ChallengeDifference
import R1Z.PV_OptB_ChallengePair
import R1Z.PV_OptB_CopySelection
import R1Z.PV_OptB_DifferentNoPole
import R1Z.PV_OptB_DistinctPoles
import R1Z.PV_OptB_FieldCard
import R1Z.PV_OptB_FixturePoleDifference
import R1Z.PV_OptB_NatCard
import R1Z.PV_OptB_PathPoles
import R1Z.PV_OptB_PathRegistry
import R1Z.PV_OptB_PathTuple
import R1Z.PV_OptB_Pigeonhole
import R1Z.PV_OptB_PoleCoordinates
import R1Z.PV_OptB_PoleDecoder
import R1Z.PV_OptB_PublicGate
import R1Z.PV_OptB_RetryControl
import R1Z.PV_OptB_WitnessFamily
set_option autoImplicit false

#print axioms R1Z.PV_OptB_AdmittedFamily.exists_distinct_admitted
#print axioms R1Z.PV_OptB_AdmittedFamily.exists_distinct_fixture_admitted
#print axioms R1Z.PV_OptB_AdmittedPoleDifference.different
#print axioms R1Z.PV_OptB_AdmittedTrace.build_admitted
#print axioms R1Z.PV_OptB_AffineTuple.affine
#print axioms R1Z.PV_OptB_AffineTuple.injective
#print axioms R1Z.PV_OptB_Cardinality.same_public_distinct_witnesses
#print axioms R1Z.PV_OptB_Cardinality.sparse_cardinality
#print axioms R1Z.PV_OptB_ChallengeDifference.different
#print axioms R1Z.PV_OptB_ChallengePair.first
#print axioms R1Z.PV_OptB_ChallengePair.second
#print axioms R1Z.PV_OptB_ChallengePair.retained
#print axioms R1Z.PV_OptB_CopySelection.select_unique
#print axioms R1Z.PV_OptB_CopySelection.producer_value
#print axioms R1Z.PV_OptB_CopySelection.consumer_value
#print axioms R1Z.PV_OptB_DifferentNoPole.different_noPole
#print axioms R1Z.PV_OptB_DistinctPoles.distinct_pole_sets
#print axioms R1Z.PV_OptB_DistinctPoles.noPole_iff_not_mem
#print axioms R1Z.PV_OptB_FieldCard.cardM
#print axioms R1Z.PV_OptB_FieldCard.cardDigest_generic
#print axioms R1Z.PV_OptB_FieldCard.cardDigest
#print axioms R1Z.PV_OptB_FieldCard.large
#print axioms R1Z.PV_OptB_FieldCard.large_for
#print axioms R1Z.PV_OptB_FixturePoleDifference.fixture
#print axioms R1Z.PV_OptB_NatCard.distinct_small_sets
#print axioms R1Z.PV_OptB_NatCard.large_for
#print axioms R1Z.PV_OptB_PathPoles.lifted_path
#print axioms R1Z.PV_OptB_PathPoles.tuple_value
#print axioms R1Z.PV_OptB_PathPoles.phi_injective
#print axioms R1Z.PV_OptB_PathPoles.phi_mem
#print axioms R1Z.PV_OptB_PathRegistry.member
#print axioms R1Z.PV_OptB_PathRegistry.descriptor
#print axioms R1Z.PV_OptB_PathRegistry.active
#print axioms R1Z.PV_OptB_PathRegistry.pattern13
#print axioms R1Z.PV_OptB_PathRegistry.value_mem
#print axioms R1Z.PV_OptB_PathTuple.right_cell
#print axioms R1Z.PV_OptB_PathTuple.tuple_shape
#print axioms R1Z.PV_OptB_Pigeonhole.distinct_small_sets
#print axioms R1Z.PV_OptB_PoleCoordinates.contains
#print axioms R1Z.PV_OptB_PoleCoordinates.bounded
#print axioms R1Z.PV_OptB_PoleCoordinates.equal_of_poleSet_equal
#print axioms R1Z.PV_OptB_PoleDecoder.no_decoder_of_opposite
#print axioms R1Z.PV_OptB_PublicGate.accepted_opposite
#print axioms R1Z.PV_OptB_PublicGate.rejected_together
#print axioms R1Z.PV_OptB_RetryControl.accepts_before_fault
#print axioms R1Z.PV_OptB_RetryControl.retries_into_fault
#print axioms R1Z.PV_OptB_RetryControl.fixed_potential_fault_is_insufficient
#print axioms R1Z.PV_OptB_WitnessFamily.path_zero
#print axioms R1Z.PV_OptB_WitnessFamily.path_coordinate
#print axioms R1Z.PV_OptB_WitnessFamily.witness_injective
#print axioms R1Z.PV_OptB_WitnessFamily.prefix_anchor_update
#print axioms R1Z.PV_OptB_WitnessFamily.rspend
#print axioms R1Z.PV_OptB_WitnessFamily.rspendPlus
#print axioms R1Z.PV_OptB_WitnessFamily.public_eq_of_root_eq
