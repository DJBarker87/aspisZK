import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- field/terminal_limb#0; complete source and owned lexical token sequences. -/
def source_tokens11_field_terminal_limb_0 : String := "[\"fn\",\"terminal_limb\",\"(\",\"value\",\":\",\"M31\",\")\",\"-\",\">\",\"u64\",\"{\",\"u64\",\":\",\":\",\"from\",\"(\",\"value\",\".\",\"0\",\")\",\"}\"]"
def owned_tokens11_field_terminal_limb_0 : String := "[\"fn\",\"terminal_limb\",\"(\",\"value\",\":\",\"M31\",\")\",\"-\",\">\",\"u64\",\"{\",\"u64\",\":\",\":\",\"from\",\"(\",\"value\",\".\",\"0\",\")\",\"}\"]"
theorem body_identity11_field_terminal_limb_0 : source_tokens11_field_terminal_limb_0 = owned_tokens11_field_terminal_limb_0 :=
  token_identity11 source_tokens11_field_terminal_limb_0
theorem body_interpretation11_field_terminal_limb_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_field_terminal_limb_0 = interpret owned_tokens11_field_terminal_limb_0 :=
  interpret_identity11 interpret _ _ body_identity11_field_terminal_limb_0
#print axioms body_identity11_field_terminal_limb_0
#print axioms body_interpretation11_field_terminal_limb_0
end PV_B3P_Binding11227
