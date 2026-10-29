import R1Z.PV_RJDec_RuntimeFields
import R1Z.PV_RJDec_TotalExtension
import R1Z.PV_RJDec_CommonCases
import R1Z.PV_RJDec_SourceFields
import R1Z.PV_RJDec_LedgerFields
import R1Z.PV_RJDec_InstalledFields
import R1Z.PV_RJDec_V047Native
import R1Z.PV_RJDec_SnapshotGuard
import R1Z.PV_RJDec_TerminalGuard
import R1Z.PV_RJDec_AfterGuard
import R1Z.PV_RJDec_PaymentPrefix
import R1Z.PV_RJDec_Factor
import R1Z.PV_RJDec_ResultCases
import R1Z.PV_RunJoin_InstalledCausalHeadline
import R1Z.PV_RunJoin_JoinedCausalHeadline
#print R1Z.PV_RJDec_RuntimeFields.execute_independent
#print R1Z.PV_RJDec_RuntimeFields.oracle_underdetermined
#print R1Z.PV_RJDec_TotalExtension.cases_iff
#print R1Z.PV_RJDec_TotalExtension.unreachable_free
#print R1Z.PV_RJDec_CommonCases.complete_pair
#print R1Z.PV_RJDec_SourceFields.fields
#print R1Z.PV_RJDec_LedgerFields.fields
#print R1Z.PV_RJDec_InstalledFields.fields
#print R1Z.PV_RJDec_V047Native.consume
#print R1Z.PV_RJDec_V047Native.identification_iff
#print R1Z.PV_RJDec_SnapshotGuard.wrong_length
#print R1Z.PV_RJDec_TerminalGuard.failure
#print R1Z.PV_RJDec_TerminalGuard.divergence
#print R1Z.PV_RJDec_TerminalGuard.wrong_length
#print R1Z.PV_RJDec_AfterGuard.failure
#print R1Z.PV_RJDec_AfterGuard.divergence
#print R1Z.PV_RJDec_AfterGuard.wrong_length
#print R1Z.PV_RJDec_PaymentPrefix.transfer_failure
#print R1Z.PV_RJDec_PaymentPrefix.transfer_divergence
#print R1Z.PV_RJDec_PaymentPrefix.withdrawal_failure
#print R1Z.PV_RJDec_PaymentPrefix.withdrawal_divergence
#print R1Z.PV_RJDec_Factor.exists_iff
#print R1Z.PV_RJDec_Factor.pair_iff
#print R1Z.PV_RJDec_ResultCases.fibres_iff
#print AspisR1.PV_2TNV_HeadlineFibre.fibre
#print R1Z.PV_RunJoin_InstalledCausalHeadline.privacy_headline_deployed_candidate
#print R1Z.PV_RunJoin_JoinedCausalHeadline.privacy_headline_deployed_candidate
#print R1Z.PV_RunJoin_Deployed.Runtime
#print R1Z.PV_RunJoin_SourceConstructor.runtime
#print R1Z.PV_RunJoin_LedgerConstructor.runtime
#print R1Z.PV_RunJoin_InstalledEndpoint.runtime
#print R1Z.PV_RunJoin_CommonSample32.complete_view
#print R1Z.PV_RunJoin_CommonObserver32.complete_pair
#print R1Z.PV_RunJoin_TrustItems
#print R1Z.PV_RunJoin_AbstractEndpoint.PV_RunJoin_Premises
#print R1Z.PV_RunJoin_Endpoint.PV_RunJoin_Premises
#print axioms R1Z.PV_RJDec_RuntimeFields.execute_independent
#print axioms R1Z.PV_RJDec_RuntimeFields.oracle_underdetermined
#print axioms R1Z.PV_RJDec_TotalExtension.cases_iff
#print axioms R1Z.PV_RJDec_TotalExtension.unreachable_free
#print axioms R1Z.PV_RJDec_CommonCases.complete_pair
#print axioms R1Z.PV_RJDec_SourceFields.fields
#print axioms R1Z.PV_RJDec_LedgerFields.fields
#print axioms R1Z.PV_RJDec_InstalledFields.fields
#print axioms R1Z.PV_RJDec_V047Native.consume
#print axioms R1Z.PV_RJDec_V047Native.identification_iff
#print axioms R1Z.PV_RJDec_SnapshotGuard.wrong_length
#print axioms R1Z.PV_RJDec_TerminalGuard.failure
#print axioms R1Z.PV_RJDec_TerminalGuard.divergence
#print axioms R1Z.PV_RJDec_TerminalGuard.wrong_length
#print axioms R1Z.PV_RJDec_AfterGuard.failure
#print axioms R1Z.PV_RJDec_AfterGuard.divergence
#print axioms R1Z.PV_RJDec_AfterGuard.wrong_length
#print axioms R1Z.PV_RJDec_PaymentPrefix.transfer_failure
#print axioms R1Z.PV_RJDec_PaymentPrefix.transfer_divergence
#print axioms R1Z.PV_RJDec_PaymentPrefix.withdrawal_failure
#print axioms R1Z.PV_RJDec_PaymentPrefix.withdrawal_divergence
#print axioms R1Z.PV_RJDec_Factor.exists_iff
#print axioms R1Z.PV_RJDec_Factor.pair_iff
#print axioms R1Z.PV_RJDec_ResultCases.fibres_iff
#print axioms AspisR1.PV_2TNV_HeadlineFibre.fibre
#print axioms R1Z.PV_RunJoin_InstalledCausalHeadline.privacy_headline_deployed_candidate
#print axioms R1Z.PV_RunJoin_JoinedCausalHeadline.privacy_headline_deployed_candidate
