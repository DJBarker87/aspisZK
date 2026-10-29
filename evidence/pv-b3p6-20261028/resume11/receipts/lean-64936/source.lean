import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- copy/row#0; complete source and owned lexical token sequences. -/
def source_tokens11_copy_row_0 : String := "[\"fn\",\"row\",\"(\",\"&\",\"self\",\",\",\"row\",\":\",\"usize\",\")\",\"-\",\">\",\"QM31\",\"{\",\"debug_assert\",\"!\",\"(\",\"row\",\"<\",\"POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1\",\")\",\";\",\"self\",\".\",\"high\",\"[\",\"row\",\">\",\">\",\"4\",\"]\",\".\",\"mul\",\"(\",\"self\",\".\",\"low\",\"[\",\"row\",\"&\",\"15\",\"]\",\")\",\"}\"]"
def owned_tokens11_copy_row_0 : String := "[\"fn\",\"row\",\"(\",\"&\",\"self\",\",\",\"row\",\":\",\"usize\",\")\",\"-\",\">\",\"QM31\",\"{\",\"debug_assert\",\"!\",\"(\",\"row\",\"<\",\"POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1\",\")\",\";\",\"self\",\".\",\"high\",\"[\",\"row\",\">\",\">\",\"4\",\"]\",\".\",\"mul\",\"(\",\"self\",\".\",\"low\",\"[\",\"row\",\"&\",\"15\",\"]\",\")\",\"}\"]"
theorem body_identity11_copy_row_0 : source_tokens11_copy_row_0 = owned_tokens11_copy_row_0 :=
  token_identity11 source_tokens11_copy_row_0
theorem body_interpretation11_copy_row_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_copy_row_0 = interpret owned_tokens11_copy_row_0 :=
  interpret_identity11 interpret _ _ body_identity11_copy_row_0
#print axioms body_identity11_copy_row_0
#print axioms body_interpretation11_copy_row_0
end PV_B3P_Binding11227
