import R1Z.PV_RunJoin_TrustAudit9Records
import R1Z.PV_RunJoin_TrustAudit9Joins
import R1Z.PV_L2_F3Recorded
import R1Z.PV_L2_F3FullSource
import R1Z.PV_L2_F3FullRetry
import R1Z.PV_L2_HeadlineF3
import R1Z.PV_L2_HeadlineJoint
import R1Z.PV_L2_RecordRefinement
import R1Z.PV_L2_F6KDot
import R1Z.PV_L2_F6Image
/- Focused audit of delivered L2 source/model results. F5 and multiproof missing objects remain recorded P work; no native trace refinement is inferred. -/
#print axioms R1Z.PV_L2_F3Recorded.scalar_erases
#print axioms R1Z.PV_L2_F3Recorded.source_scalar_erases
#print axioms R1Z.PV_L2_F3Recorded.collect_erases
#print axioms R1Z.PV_L2_F3Recorded.qm31_erases
#print axioms R1Z.PV_L2_F3FullSource.erases
#print axioms R1Z.PV_L2_F3FullSource.arrays_erases
#print axioms R1Z.PV_L2_F3FullSource.pair_erases
#print axioms R1Z.PV_L2_F3FullSource.observed_erases
#print axioms R1Z.PV_L2_F3FullRetry.full_l1_erases
#print axioms R1Z.PV_L2_F3FullRetry.rejected_prefix
#print axioms R1Z.PV_L2_F3FullRetry.stopping_prefix
#print axioms R1Z.PV_L2_F3FullRetry.rejected_rom_prefix
#print axioms R1Z.PV_L2_F3FullRetry.l1_events
#print axioms R1Z.PV_L2_HeadlineF3.absorption_actual
#print axioms R1Z.PV_L2_HeadlineJoint.original_refinement
#print axioms R1Z.PV_L2_HeadlineJoint.agreement_exact
#print axioms R1Z.PV_L2_RecordRefinement.bind_erases
#print axioms R1Z.PV_L2_F6KDot.loop_erases
#print axioms R1Z.PV_L2_F6KDot.kdot_erases
#print axioms R1Z.PV_L2_F6Image.loop_erases
#print axioms R1Z.PV_L2_F6Image.image_erases
#print R1Z.PV_L2_Premises.PV_L2_Premises
#check @R1Z.PV_L2_HeadlineJoint.original_refinement
#check @R1Z.PV_L2_HeadlineJoint.agreement_exact
#print R1Z.PV_RunJoin_TrustItems
#check @R1Z.PV_RunJoin_JoinedCausalHeadline.proofs
