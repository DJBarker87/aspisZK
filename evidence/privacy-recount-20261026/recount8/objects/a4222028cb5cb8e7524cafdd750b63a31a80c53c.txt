import R1Z.PV_L2_Headline
import R1Z.PV_L2_HeadlineJoint
import R1Z.PV_L2_PremisesBound
import R1Z.PV_L2_F3AttemptSource
import R1Z.PV_L2_F6Sharing
import R1Z.PV_L2_F5Mle
import R1Z.PV_L2_F6BCond
import R1Z.PV_L2_F6Half
import R1Z.PV_L2_F6IdentityRow
/-! Focused source/model audit. The existing complete native event-producer
and source/security trace joins remain explicit, on the SAME coupling. -/
#print R1Z.PV_L2_Premises.PV_L2_Premises
#check @R1Z.PV_L2_PremisesBound.joint_test_bound
#check @R1Z.PV_L2_F3AttemptSource.owner
#print axioms R1Z.PV_L2_Headline.deployed_parser
#print axioms R1Z.PV_L2_Headline.deployed_source_carrier
#print axioms R1Z.PV_L2_Headline.real_to_lazy_actual
#print axioms R1Z.PV_L2_Headline.absorption_actual
#print axioms R1Z.PV_L2_HeadlineJoint.original_refinement
#print axioms R1Z.PV_L2_HeadlineJoint.agreement_exact
#print axioms R1Z.PV_L2_PremisesBound.joint_test_bound
#print axioms R1Z.PV_L2_Premises.same_coupling
#print axioms R1Z.PV_L2_F3AttemptSource.source_projection
#print axioms R1Z.PV_L2_F3AttemptSource.owned_projection
#print axioms R1Z.PV_L2_F3AttemptSource.complete_l1
#print axioms R1Z.PV_L2_F6Sharing.cursor_joint
#print axioms R1Z.PV_L2_F6Sharing.singleton_layer
#print axioms R1Z.PV_L2_F6Sharing.singleton_count
#print axioms R1Z.PV_L2_F6Sharing.request_depths
#print axioms R1Z.PV_L2_F6Sharing.payload_erasure
#print axioms R1Z.PV_L2_F5Mle.erases
#print axioms R1Z.PV_L2_F6BCond.erases
#print axioms R1Z.PV_L2_F6Half.erases
#print axioms R1Z.PV_L2_F6IdentityRow.erases
