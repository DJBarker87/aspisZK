import R1Z.PV_RunJoin_NullifierSource17
import R1Z.PV_RunJoin_CompilerChecks17
import R1Z.PV_RunJoin_AppendNative17
import R1Z.PV_RunJoin_BankRow17
import R1Z.PV_RunJoin_ParentValue17
import R1Z.PV_RunJoin_ZeroValidation17

/-! Focused audit of accepted runjoin17 roots. The endpoint audit is blocked
by missing source authority and is not claimed by this module. -/
#print axioms R1Z.PV_RunJoin_NullifierSource17.transfer
#print axioms R1Z.PV_RunJoin_NullifierSource17.withdrawal
#print axioms R1Z.PV_RunJoin_OutputPair17.transfer
#print axioms R1Z.PV_RunJoin_OutputPair17.withdrawal
#print axioms R1Z.PV_RunJoin_AppendNative17.transfer
#print axioms R1Z.PV_RunJoin_AppendNative17.withdrawal
#print axioms R1Z.PV_RunJoin_BankRow17.row
#print axioms R1Z.PV_RunJoin_ParentValue17.source
#print axioms R1Z.PV_RunJoin_ZeroTree17.frontier
#print axioms R1Z.PV_RunJoin_ZeroTree17.eq_self
#print axioms R1Z.PV_RunJoin_ZeroValidation17.fixture
#print axioms R1Z.PV_RunJoin_CompilerChecks17.transfer_lane
#print axioms R1Z.PV_RunJoin_CompilerChecks17.transfer_anchor
#print axioms R1Z.PV_RunJoin_CompilerChecks17.transfer_nullifier
#print axioms R1Z.PV_RunJoin_CompilerChecks17.transfer_change
#print axioms R1Z.PV_RunJoin_CompilerChecks17.transfer_recipient
#print axioms R1Z.PV_RunJoin_CompilerChecks17.withdrawal_lane
#print axioms R1Z.PV_RunJoin_CompilerChecks17.withdrawal_anchor
#print axioms R1Z.PV_RunJoin_CompilerChecks17.withdrawal_nullifier
#print axioms R1Z.PV_RunJoin_CompilerChecks17.withdrawal_change
