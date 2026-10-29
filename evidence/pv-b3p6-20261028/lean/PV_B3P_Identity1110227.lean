import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/scalar_lanes#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_scalar_lanes_0 : String := "[\"fn\",\"scalar_lanes\",\"(\",\"variant\",\":\",\"CompiledVariant\",\",\",\"withdrawal_amount_present\",\":\",\"bool\",\",\",\"input_asset\",\":\",\"QM31\",\",\",\"mut\",\"output_scalar\",\":\",\"QM31\",\",\",\"private_transfer_term\",\":\",\"QM31\",\",\",\"withdrawal_term\",\":\",\"QM31\",\",\",\")\",\"-\",\">\",\"[\",\"QM31\",\";\",\"2\",\"]\",\"{\",\"match\",\"variant\",\"{\",\"CompiledVariant\",\":\",\":\",\"PrivateTransfer\",\"=\",\">\",\"{\",\"output_scalar\",\"=\",\"output_scalar\",\".\",\"add\",\"(\",\"private_transfer_term\",\")\",\";\",\"}\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\"=\",\">\",\"{\",\"if\",\"withdrawal_amount_present\",\"{\",\"output_scalar\",\"=\",\"output_scalar\",\".\",\"add\",\"(\",\"withdrawal_term\",\")\",\";\",\"}\",\"}\",\"}\",\"[\",\"input_asset\",\",\",\"output_scalar\",\"]\",\"}\"]"
def owned_tokens11_terminal_scalar_lanes_0 : String := "[\"fn\",\"scalar_lanes\",\"(\",\"variant\",\":\",\"CompiledVariant\",\",\",\"withdrawal_amount_present\",\":\",\"bool\",\",\",\"input_asset\",\":\",\"QM31\",\",\",\"mut\",\"output_scalar\",\":\",\"QM31\",\",\",\"private_transfer_term\",\":\",\"QM31\",\",\",\"withdrawal_term\",\":\",\"QM31\",\",\",\")\",\"-\",\">\",\"[\",\"QM31\",\";\",\"2\",\"]\",\"{\",\"match\",\"variant\",\"{\",\"CompiledVariant\",\":\",\":\",\"PrivateTransfer\",\"=\",\">\",\"{\",\"output_scalar\",\"=\",\"output_scalar\",\".\",\"add\",\"(\",\"private_transfer_term\",\")\",\";\",\"}\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\"=\",\">\",\"{\",\"if\",\"withdrawal_amount_present\",\"{\",\"output_scalar\",\"=\",\"output_scalar\",\".\",\"add\",\"(\",\"withdrawal_term\",\")\",\";\",\"}\",\"}\",\"}\",\"[\",\"input_asset\",\",\",\"output_scalar\",\"]\",\"}\"]"
theorem body_identity11_terminal_scalar_lanes_0 : source_tokens11_terminal_scalar_lanes_0 = owned_tokens11_terminal_scalar_lanes_0 :=
  token_identity11 source_tokens11_terminal_scalar_lanes_0
theorem body_interpretation11_terminal_scalar_lanes_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_scalar_lanes_0 = interpret owned_tokens11_terminal_scalar_lanes_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_scalar_lanes_0
#print axioms body_identity11_terminal_scalar_lanes_0
#print axioms body_interpretation11_terminal_scalar_lanes_0
end PV_B3P_Binding11227
