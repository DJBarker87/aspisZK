import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/initial_variant_selectors#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_initial_variant_selectors_0 : String := "[\"fn\",\"initial_variant_selectors\",\"(\",\"variant\",\":\",\"CompiledVariant\",\",\",\"high27\",\":\",\"QM31\",\",\",\"high28\",\":\",\"QM31\",\",\",\"high29\",\":\",\"QM31\",\",\",\")\",\"-\",\">\",\"(\",\"QM31\",\",\",\"QM31\",\",\",\"QM31\",\",\",\"QM31\",\")\",\"{\",\"match\",\"variant\",\"{\",\"CompiledVariant\",\":\",\":\",\"PrivateTransfer\",\"=\",\">\",\"(\",\"high27\",\",\",\"QM31\",\":\",\":\",\"ZERO\",\",\",\"high27\",\".\",\"add\",\"(\",\"high28\",\")\",\",\",\"high29\",\",\",\")\",\",\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\"=\",\">\",\"(\",\"QM31\",\":\",\":\",\"ZERO\",\",\",\"high27\",\".\",\"add\",\"(\",\"high28\",\")\",\".\",\"add\",\"(\",\"high29\",\")\",\",\",\"QM31\",\":\",\":\",\"ZERO\",\",\",\"QM31\",\":\",\":\",\"ZERO\",\",\",\")\",\",\",\"}\",\"}\"]"
def owned_tokens11_terminal_initial_variant_selectors_0 : String := "[\"fn\",\"initial_variant_selectors\",\"(\",\"variant\",\":\",\"CompiledVariant\",\",\",\"high27\",\":\",\"QM31\",\",\",\"high28\",\":\",\"QM31\",\",\",\"high29\",\":\",\"QM31\",\",\",\")\",\"-\",\">\",\"(\",\"QM31\",\",\",\"QM31\",\",\",\"QM31\",\",\",\"QM31\",\")\",\"{\",\"match\",\"variant\",\"{\",\"CompiledVariant\",\":\",\":\",\"PrivateTransfer\",\"=\",\">\",\"(\",\"high27\",\",\",\"QM31\",\":\",\":\",\"ZERO\",\",\",\"high27\",\".\",\"add\",\"(\",\"high28\",\")\",\",\",\"high29\",\",\",\")\",\",\",\"CompiledVariant\",\":\",\":\",\"Withdrawal\",\"=\",\">\",\"(\",\"QM31\",\":\",\":\",\"ZERO\",\",\",\"high27\",\".\",\"add\",\"(\",\"high28\",\")\",\".\",\"add\",\"(\",\"high29\",\")\",\",\",\"QM31\",\":\",\":\",\"ZERO\",\",\",\"QM31\",\":\",\":\",\"ZERO\",\",\",\")\",\",\",\"}\",\"}\"]"
theorem body_identity11_terminal_initial_variant_selectors_0 : source_tokens11_terminal_initial_variant_selectors_0 = owned_tokens11_terminal_initial_variant_selectors_0 :=
  token_identity11 source_tokens11_terminal_initial_variant_selectors_0
theorem body_interpretation11_terminal_initial_variant_selectors_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_initial_variant_selectors_0 = interpret owned_tokens11_terminal_initial_variant_selectors_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_initial_variant_selectors_0
#print axioms body_identity11_terminal_initial_variant_selectors_0
#print axioms body_interpretation11_terminal_initial_variant_selectors_0
end PV_B3P_Binding11227
