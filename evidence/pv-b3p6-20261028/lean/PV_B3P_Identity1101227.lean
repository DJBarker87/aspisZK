import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/bounded_append_carry#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_bounded_append_carry_0 : String := "[\"fn\",\"bounded_append_carry\",\"(\",\"mut\",\"index\",\":\",\"u64\",\")\",\"-\",\">\",\"usize\",\"{\",\"let\",\"mut\",\"carry\",\"=\",\"0usize\",\";\",\"while\",\"carry\",\"<\",\"20\",\"{\",\"if\",\"index\",\"&\",\"1\",\"=\",\"=\",\"0\",\"{\",\"return\",\"carry\",\";\",\"}\",\"index\",\">\",\">\",\"=\",\"1u32\",\";\",\"carry\",\"+\",\"=\",\"1\",\";\",\"}\",\"carry\",\"}\"]"
def owned_tokens11_terminal_bounded_append_carry_0 : String := "[\"fn\",\"bounded_append_carry\",\"(\",\"mut\",\"index\",\":\",\"u64\",\")\",\"-\",\">\",\"usize\",\"{\",\"let\",\"mut\",\"carry\",\"=\",\"0usize\",\";\",\"while\",\"carry\",\"<\",\"20\",\"{\",\"if\",\"index\",\"&\",\"1\",\"=\",\"=\",\"0\",\"{\",\"return\",\"carry\",\";\",\"}\",\"index\",\">\",\">\",\"=\",\"1u32\",\";\",\"carry\",\"+\",\"=\",\"1\",\";\",\"}\",\"carry\",\"}\"]"
theorem body_identity11_terminal_bounded_append_carry_0 : source_tokens11_terminal_bounded_append_carry_0 = owned_tokens11_terminal_bounded_append_carry_0 :=
  token_identity11 source_tokens11_terminal_bounded_append_carry_0
theorem body_interpretation11_terminal_bounded_append_carry_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_bounded_append_carry_0 = interpret owned_tokens11_terminal_bounded_append_carry_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_bounded_append_carry_0
#print axioms body_identity11_terminal_bounded_append_carry_0
#print axioms body_interpretation11_terminal_bounded_append_carry_0
end PV_B3P_Binding11227
