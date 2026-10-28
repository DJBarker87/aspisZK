import R1Z.PV_RunJoin_TransferIdentification16
import R1Z.PV_RunJoin_OutputChecks16
import R1Z.PV_RunJoin_PathChecks16
import R1Z.PV_RunJoin_SelectedCheck16
import R1Z.PV_RunJoin_Nullifier16
import R1Z.PV_RunJoin_CallbackPermutation16
import R1Z.PV_RunJoin_HoistedCaller16
import R1Z.PV_RunJoin_CompilerDictionary16
import R1Z.PV_RunJoin_FixtureReturns16
/- Focused audit of the concrete extraction and its nominal adapter. -/
#print R1Z.BuilderForestAdmissionPort.Records
#print axioms PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.records
#print axioms R1Z.PV_RunJoin_RecordsAdapter16.R_shipped
#print axioms R1Z.PV_RunJoin_TransferIdentification16.transfer
#print axioms R1Z.PV_RunJoin_WithdrawalIdentification16.withdrawal
#print axioms R1Z.PV_RunJoin_GeneralIdentification16.with_roots
#print axioms R1Z.PV_RunJoin_GeneralIdentification16.general
#print axioms R1Z.PV_Src_RootHelper.source
#print axioms R1Z.PV_RunJoin_CompilerDictionary16.dictionary
#print axioms R1Z.PV_RunJoin_CompilerDictionary16.compiler
#print axioms R1Z.PV_RunJoin_CompilerDictionary16.newRecords
#print axioms R1Z.PV_RunJoin_FixtureReturns16.transfer
#print axioms R1Z.PV_RunJoin_FixtureReturns16.withdrawal

#print axioms R1Z.PV_RunJoin_HoistedCaller16.frozen
#print axioms R1Z.PV_RunJoin_HoistedCaller16.original

#print axioms R1Z.PV_RunJoin_CallbackPermutation16.source

/- Fixture portion of the combined focused audit. -/
#print axioms R1Z.PV_RunJoin_SelectedCheck16.transfer
#print axioms R1Z.PV_RunJoin_SelectedCheck16.withdrawal
#print axioms R1Z.PV_RunJoin_Nullifier16.transfer
#print axioms R1Z.PV_RunJoin_Nullifier16.withdrawal
#print axioms R1Z.PV_RunJoin_PairLeafCheck16.leaf
#print axioms R1Z.PV_RunJoin_PathChecks16.transfer_pair
#print axioms R1Z.PV_RunJoin_PathChecks16.withdrawal_pair
#print axioms R1Z.PV_RunJoin_PathChecks16.transfer_lane
#print axioms R1Z.PV_RunJoin_PathChecks16.withdrawal_lane
#print axioms R1Z.PV_RunJoin_PathChecks16.transfer_anchor
#print axioms R1Z.PV_RunJoin_PathChecks16.withdrawal_anchor
#print axioms R1Z.PV_RunJoin_OutputChecks16.recipient
#print axioms R1Z.PV_RunJoin_OutputChecks16.transfer_change
#print axioms R1Z.PV_RunJoin_OutputChecks16.withdrawal_change
