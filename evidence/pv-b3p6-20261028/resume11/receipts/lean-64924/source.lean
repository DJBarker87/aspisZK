import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/variant_expected_output#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_variant_expected_output_0 : String := "[\"fn\",\"variant_expected_output\",\"(\",\"variant\",\":\",\"CompiledVariant\",\")\",\"-\",\">\",\"M31\",\"{\",\"match\",\"variant\",\"{\",\"CompiledVariant\",\":\",\":\",\"PrivateTransfer\",\"=\",\">\",\"M31\",\"(\",\"1\",\")\",\",\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\"=\",\">\",\"M31\",\"(\",\"0\",\")\",\",\",\"}\",\"}\"]"
def owned_tokens11_terminal_variant_expected_output_0 : String := "[\"fn\",\"variant_expected_output\",\"(\",\"variant\",\":\",\"CompiledVariant\",\")\",\"-\",\">\",\"M31\",\"{\",\"match\",\"variant\",\"{\",\"CompiledVariant\",\":\",\":\",\"PrivateTransfer\",\"=\",\">\",\"M31\",\"(\",\"1\",\")\",\",\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\"=\",\">\",\"M31\",\"(\",\"0\",\")\",\",\",\"}\",\"}\"]"
theorem body_identity11_terminal_variant_expected_output_0 : source_tokens11_terminal_variant_expected_output_0 = owned_tokens11_terminal_variant_expected_output_0 :=
  token_identity11 source_tokens11_terminal_variant_expected_output_0
theorem body_interpretation11_terminal_variant_expected_output_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_variant_expected_output_0 = interpret owned_tokens11_terminal_variant_expected_output_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_variant_expected_output_0
#print axioms body_identity11_terminal_variant_expected_output_0
#print axioms body_interpretation11_terminal_variant_expected_output_0
end PV_B3P_Binding11227
