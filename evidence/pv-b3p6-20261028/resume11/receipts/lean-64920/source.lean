import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/semantic#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_semantic_0 : String := "[\"fn\",\"semantic\",\"(\",\"self\",\")\",\"-\",\">\",\"SemanticPublic\",\"{\",\"match\",\"self\",\"{\",\"Self\",\":\",\":\",\"Transfer\",\"(\",\"public\",\",\",\"transition\",\")\",\"=\",\">\",\"private_public\",\"(\",\"public\",\",\",\"transition\",\")\",\",\",\"Self\",\":\",\":\",\"Withdrawal\",\"(\",\"public\",\",\",\"transition\",\")\",\"=\",\">\",\"withdrawal_public\",\"(\",\"public\",\",\",\"transition\",\")\",\",\",\"}\",\"}\"]"
def owned_tokens11_terminal_semantic_0 : String := "[\"fn\",\"semantic\",\"(\",\"self\",\")\",\"-\",\">\",\"SemanticPublic\",\"{\",\"match\",\"self\",\"{\",\"Self\",\":\",\":\",\"Transfer\",\"(\",\"public\",\",\",\"transition\",\")\",\"=\",\">\",\"private_public\",\"(\",\"public\",\",\",\"transition\",\")\",\",\",\"Self\",\":\",\":\",\"Withdrawal\",\"(\",\"public\",\",\",\"transition\",\")\",\"=\",\">\",\"withdrawal_public\",\"(\",\"public\",\",\",\"transition\",\")\",\",\",\"}\",\"}\"]"
theorem body_identity11_terminal_semantic_0 : source_tokens11_terminal_semantic_0 = owned_tokens11_terminal_semantic_0 :=
  token_identity11 source_tokens11_terminal_semantic_0
theorem body_interpretation11_terminal_semantic_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_semantic_0 = interpret owned_tokens11_terminal_semantic_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_semantic_0
#print axioms body_identity11_terminal_semantic_0
#print axioms body_interpretation11_terminal_semantic_0
end PV_B3P_Binding11227
