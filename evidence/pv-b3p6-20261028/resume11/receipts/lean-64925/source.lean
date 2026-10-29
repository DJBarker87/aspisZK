import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/withdrawal_public#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_withdrawal_public_0 : String := "[\"fn\",\"withdrawal_public\",\"<\",\"'\",\"a\",\">\",\"(\",\"public\",\":\",\"&\",\"PoolV1WithdrawalPublicV1\",\",\",\"transition\",\":\",\"&\",\"'\",\"a\",\"PoolV1PairLatePublicStatementV1\",\",\",\")\",\"-\",\">\",\"SemanticPublic\",\"{\",\"SemanticPublic\",\"{\",\"variant\",\":\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\",\",\"pool\",\":\",\"public\",\".\",\"pool\",\",\",\"deployment_domain\",\":\",\"public\",\".\",\"deployment_domain\",\",\",\"anchor\",\":\",\"public\",\".\",\"anchor_root\",\",\",\"nullifier\",\":\",\"public\",\".\",\"nullifier\",\",\",\"asset_id\",\":\",\"public\",\".\",\"asset_id\",\",\",\"recipient\",\":\",\"None\",\",\",\"change\",\":\",\"public\",\".\",\"change_commitment\",\",\",\"withdrawal_amount\",\":\",\"Some\",\"(\",\"public\",\".\",\"amount\",\")\",\",\",\"transition\",\":\",\"*\",\"transition\",\",\",\"}\",\"}\"]"
def owned_tokens11_terminal_withdrawal_public_0 : String := "[\"fn\",\"withdrawal_public\",\"<\",\"'\",\"a\",\">\",\"(\",\"public\",\":\",\"&\",\"PoolV1WithdrawalPublicV1\",\",\",\"transition\",\":\",\"&\",\"'\",\"a\",\"PoolV1PairLatePublicStatementV1\",\",\",\")\",\"-\",\">\",\"SemanticPublic\",\"{\",\"SemanticPublic\",\"{\",\"variant\",\":\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\",\",\"pool\",\":\",\"public\",\".\",\"pool\",\",\",\"deployment_domain\",\":\",\"public\",\".\",\"deployment_domain\",\",\",\"anchor\",\":\",\"public\",\".\",\"anchor_root\",\",\",\"nullifier\",\":\",\"public\",\".\",\"nullifier\",\",\",\"asset_id\",\":\",\"public\",\".\",\"asset_id\",\",\",\"recipient\",\":\",\"None\",\",\",\"change\",\":\",\"public\",\".\",\"change_commitment\",\",\",\"withdrawal_amount\",\":\",\"Some\",\"(\",\"public\",\".\",\"amount\",\")\",\",\",\"transition\",\":\",\"*\",\"transition\",\",\",\"}\",\"}\"]"
theorem body_identity11_terminal_withdrawal_public_0 : source_tokens11_terminal_withdrawal_public_0 = owned_tokens11_terminal_withdrawal_public_0 :=
  token_identity11 source_tokens11_terminal_withdrawal_public_0
theorem body_interpretation11_terminal_withdrawal_public_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_withdrawal_public_0 = interpret owned_tokens11_terminal_withdrawal_public_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_withdrawal_public_0
#print axioms body_identity11_terminal_withdrawal_public_0
#print axioms body_interpretation11_terminal_withdrawal_public_0
end PV_B3P_Binding11227
