import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/transition#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_transition_0 : String := "[\"fn\",\"transition\",\"(\",\"self\",\")\",\"-\",\">\",\"&\",\"'\",\"a\",\"PoolV1PairLatePublicStatementV1\",\"{\",\"match\",\"self\",\"{\",\"Self\",\":\",\":\",\"Transfer\",\"(\",\"_\",\",\",\"t\",\")\",\"|\",\"Self\",\":\",\":\",\"Withdrawal\",\"(\",\"_\",\",\",\"t\",\")\",\"=\",\">\",\"t\",\"}\",\"}\"]"
def owned_tokens11_terminal_transition_0 : String := "[\"fn\",\"transition\",\"(\",\"self\",\")\",\"-\",\">\",\"&\",\"'\",\"a\",\"PoolV1PairLatePublicStatementV1\",\"{\",\"match\",\"self\",\"{\",\"Self\",\":\",\":\",\"Transfer\",\"(\",\"_\",\",\",\"t\",\")\",\"|\",\"Self\",\":\",\":\",\"Withdrawal\",\"(\",\"_\",\",\",\"t\",\")\",\"=\",\">\",\"t\",\"}\",\"}\"]"
theorem body_identity11_terminal_transition_0 : source_tokens11_terminal_transition_0 = owned_tokens11_terminal_transition_0 :=
  token_identity11 source_tokens11_terminal_transition_0
theorem body_interpretation11_terminal_transition_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_transition_0 = interpret owned_tokens11_terminal_transition_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_transition_0
#print axioms body_identity11_terminal_transition_0
#print axioms body_interpretation11_terminal_transition_0
end PV_B3P_Binding11227
