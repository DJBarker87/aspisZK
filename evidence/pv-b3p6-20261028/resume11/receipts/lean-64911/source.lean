import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/empty_root#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_empty_root_0 : String := "[\"fn\",\"empty_root\",\"(\",\"level\",\":\",\"usize\",\")\",\"-\",\">\",\"Digest\",\"{\",\"let\",\"words\",\"=\",\"constants\",\":\",\":\",\"POOL_V1_PAIR_EMPTY_ROOTS_V1\",\"[\",\"level\",\"]\",\";\",\"[\",\"M31\",\"(\",\"words\",\"[\",\"0\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"1\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"2\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"3\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"4\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"5\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"6\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"7\",\"]\",\")\",\"]\",\"}\"]"
def owned_tokens11_terminal_empty_root_0 : String := "[\"fn\",\"empty_root\",\"(\",\"level\",\":\",\"usize\",\")\",\"-\",\">\",\"Digest\",\"{\",\"let\",\"words\",\"=\",\"constants\",\":\",\":\",\"POOL_V1_PAIR_EMPTY_ROOTS_V1\",\"[\",\"level\",\"]\",\";\",\"[\",\"M31\",\"(\",\"words\",\"[\",\"0\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"1\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"2\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"3\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"4\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"5\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"6\",\"]\",\")\",\",\",\"M31\",\"(\",\"words\",\"[\",\"7\",\"]\",\")\",\"]\",\"}\"]"
theorem body_identity11_terminal_empty_root_0 : source_tokens11_terminal_empty_root_0 = owned_tokens11_terminal_empty_root_0 :=
  token_identity11 source_tokens11_terminal_empty_root_0
theorem body_interpretation11_terminal_empty_root_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_empty_root_0 = interpret owned_tokens11_terminal_empty_root_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_empty_root_0
#print axioms body_identity11_terminal_empty_root_0
#print axioms body_interpretation11_terminal_empty_root_0
end PV_B3P_Binding11227
