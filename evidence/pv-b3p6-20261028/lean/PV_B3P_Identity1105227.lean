import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/fields#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_fields_0 : String := "[\"fn\",\"fields\",\"(\",\"out\",\":\",\"&\",\"mut\",\"Vec\",\"<\",\"u8\",\">\",\",\",\"values\",\":\",\"&\",\"[\",\"M31\",\"]\",\")\",\"-\",\">\",\"Result\",\"<\",\"(\",\")\",\",\",\"Error\",\">\",\"{\",\"for\",\"value\",\"in\",\"values\",\"{\",\"if\",\"value\",\".\",\"0\",\">\",\"=\",\"aspis_core\",\":\",\":\",\"field\",\":\",\":\",\"P\",\"{\",\"return\",\"Err\",\"(\",\"Error\",\":\",\":\",\"Public\",\")\",\";\",\"}\",\"out\",\".\",\"extend_from_slice\",\"(\",\"&\",\"value\",\".\",\"0\",\".\",\"to_le_bytes\",\"(\",\")\",\")\",\";\",\"}\",\"Ok\",\"(\",\"(\",\")\",\")\",\"}\"]"
def owned_tokens11_terminal_fields_0 : String := "[\"fn\",\"fields\",\"(\",\"out\",\":\",\"&\",\"mut\",\"Vec\",\"<\",\"u8\",\">\",\",\",\"values\",\":\",\"&\",\"[\",\"M31\",\"]\",\")\",\"-\",\">\",\"Result\",\"<\",\"(\",\")\",\",\",\"Error\",\">\",\"{\",\"for\",\"value\",\"in\",\"values\",\"{\",\"if\",\"value\",\".\",\"0\",\">\",\"=\",\"aspis_core\",\":\",\":\",\"field\",\":\",\":\",\"P\",\"{\",\"return\",\"Err\",\"(\",\"Error\",\":\",\":\",\"Public\",\")\",\";\",\"}\",\"out\",\".\",\"extend_from_slice\",\"(\",\"&\",\"value\",\".\",\"0\",\".\",\"to_le_bytes\",\"(\",\")\",\")\",\";\",\"}\",\"Ok\",\"(\",\"(\",\")\",\")\",\"}\"]"
theorem body_identity11_terminal_fields_0 : source_tokens11_terminal_fields_0 = owned_tokens11_terminal_fields_0 :=
  token_identity11 source_tokens11_terminal_fields_0
theorem body_interpretation11_terminal_fields_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_fields_0 = interpret owned_tokens11_terminal_fields_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_fields_0
#print axioms body_identity11_terminal_fields_0
#print axioms body_interpretation11_terminal_fields_0
end PV_B3P_Binding11227
