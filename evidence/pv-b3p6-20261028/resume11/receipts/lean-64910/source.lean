import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/copy_variant#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_copy_variant_0 : String := "[\"fn\",\"copy_variant\",\"(\",\"variant\",\":\",\"CompiledVariant\",\")\",\"-\",\">\",\"PoolV1PairForestCompiledVariantV1\",\"{\",\"match\",\"variant\",\"{\",\"CompiledVariant\",\":\",\":\",\"PrivateTransfer\",\"=\",\">\",\"PoolV1PairForestCompiledVariantV1\",\":\",\":\",\"PrivateTransfer\",\",\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\"=\",\">\",\"PoolV1PairForestCompiledVariantV1\",\":\",\":\",\"Withdrawal\",\",\",\"}\",\"}\"]"
def owned_tokens11_terminal_copy_variant_0 : String := "[\"fn\",\"copy_variant\",\"(\",\"variant\",\":\",\"CompiledVariant\",\")\",\"-\",\">\",\"PoolV1PairForestCompiledVariantV1\",\"{\",\"match\",\"variant\",\"{\",\"CompiledVariant\",\":\",\":\",\"PrivateTransfer\",\"=\",\">\",\"PoolV1PairForestCompiledVariantV1\",\":\",\":\",\"PrivateTransfer\",\",\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\"=\",\">\",\"PoolV1PairForestCompiledVariantV1\",\":\",\":\",\"Withdrawal\",\",\",\"}\",\"}\"]"
theorem body_identity11_terminal_copy_variant_0 : source_tokens11_terminal_copy_variant_0 = owned_tokens11_terminal_copy_variant_0 :=
  token_identity11 source_tokens11_terminal_copy_variant_0
theorem body_interpretation11_terminal_copy_variant_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_copy_variant_0 = interpret owned_tokens11_terminal_copy_variant_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_copy_variant_0
#print axioms body_identity11_terminal_copy_variant_0
#print axioms body_interpretation11_terminal_copy_variant_0
end PV_B3P_Binding11227
