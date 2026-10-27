import JHf_Carrier7
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toVerifierPolicyV1 (value : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.VerifierPolicyV1 :=
  {flags:=value.flags,registry_program:=value.registry_program,registry_authority:=value.registry_authority,policy_binding:=value.policy_binding}
def fromVerifierPolicyV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.VerifierPolicyV1) : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1 :=
  {flags:=value.flags,registry_program:=value.registry_program,registry_authority:=value.registry_authority,policy_binding:=value.policy_binding}
theorem from_toVerifierPolicyV1 (v : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1) : fromVerifierPolicyV1 (toVerifierPolicyV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1,fromVerifierPolicyV1,toVerifierPolicyV1]
  all_goals rfl
#print axioms from_toVerifierPolicyV1
end AspisR1.JHf_Carrier
