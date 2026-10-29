import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- copy/active#0; complete source and owned lexical token sequences. -/
def source_tokens11_copy_active_0 : String := "[\"fn\",\"active\",\"(\",\"&\",\"self\",\")\",\"-\",\">\",\"QM31\",\"{\",\"#\",\"[\",\"cfg\",\"(\",\"not\",\"(\",\"feature\",\"=\",\"\\\"optimized-terminal\\\"\",\")\",\")\",\"]\",\"return\",\"self\",\".\",\"active_literal\",\"(\",\")\",\";\",\"#\",\"[\",\"cfg\",\"(\",\"feature\",\"=\",\"\\\"optimized-terminal\\\"\",\")\",\"]\",\"return\",\"self\",\".\",\"active_mask_basis\",\"(\",\")\",\";\",\"}\"]"
def owned_tokens11_copy_active_0 : String := "[\"fn\",\"active\",\"(\",\"&\",\"self\",\")\",\"-\",\">\",\"QM31\",\"{\",\"#\",\"[\",\"cfg\",\"(\",\"not\",\"(\",\"feature\",\"=\",\"\\\"optimized-terminal\\\"\",\")\",\")\",\"]\",\"return\",\"self\",\".\",\"active_literal\",\"(\",\")\",\";\",\"#\",\"[\",\"cfg\",\"(\",\"feature\",\"=\",\"\\\"optimized-terminal\\\"\",\")\",\"]\",\"return\",\"self\",\".\",\"active_mask_basis\",\"(\",\")\",\";\",\"}\"]"
theorem body_identity11_copy_active_0 : source_tokens11_copy_active_0 = owned_tokens11_copy_active_0 :=
  token_identity11 source_tokens11_copy_active_0
theorem body_interpretation11_copy_active_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_copy_active_0 = interpret owned_tokens11_copy_active_0 :=
  interpret_identity11 interpret _ _ body_identity11_copy_active_0
#print axioms body_identity11_copy_active_0
#print axioms body_interpretation11_copy_active_0
end PV_B3P_Binding11227
