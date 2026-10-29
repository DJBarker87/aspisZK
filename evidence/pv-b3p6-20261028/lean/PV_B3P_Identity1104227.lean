import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/equality_factor#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_equality_factor_0 : String := "[\"fn\",\"equality_factor\",\"(\",\"a\",\":\",\"QM31\",\",\",\"b\",\":\",\"QM31\",\")\",\"-\",\">\",\"QM31\",\"{\",\"let\",\"ab\",\"=\",\"a\",\".\",\"mul\",\"(\",\"b\",\")\",\";\",\"QM31\",\":\",\":\",\"ONE\",\".\",\"sub\",\"(\",\"a\",\")\",\".\",\"sub\",\"(\",\"b\",\")\",\".\",\"add\",\"(\",\"ab\",\")\",\".\",\"add\",\"(\",\"ab\",\")\",\"}\"]"
def owned_tokens11_terminal_equality_factor_0 : String := "[\"fn\",\"equality_factor\",\"(\",\"a\",\":\",\"QM31\",\",\",\"b\",\":\",\"QM31\",\")\",\"-\",\">\",\"QM31\",\"{\",\"let\",\"ab\",\"=\",\"a\",\".\",\"mul\",\"(\",\"b\",\")\",\";\",\"QM31\",\":\",\":\",\"ONE\",\".\",\"sub\",\"(\",\"a\",\")\",\".\",\"sub\",\"(\",\"b\",\")\",\".\",\"add\",\"(\",\"ab\",\")\",\".\",\"add\",\"(\",\"ab\",\")\",\"}\"]"
theorem body_identity11_terminal_equality_factor_0 : source_tokens11_terminal_equality_factor_0 = owned_tokens11_terminal_equality_factor_0 :=
  token_identity11 source_tokens11_terminal_equality_factor_0
theorem body_interpretation11_terminal_equality_factor_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_equality_factor_0 = interpret owned_tokens11_terminal_equality_factor_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_equality_factor_0
#print axioms body_identity11_terminal_equality_factor_0
#print axioms body_interpretation11_terminal_equality_factor_0
end PV_B3P_Binding11227
