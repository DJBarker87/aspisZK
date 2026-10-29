import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- terminal/selected_claim#0; complete source and owned lexical token sequences. -/
def source_tokens11_terminal_selected_claim_0 : String := "[\"fn\",\"selected_claim\",\"(\",\"claims\",\":\",\"&\",\"[\",\"QM31\",\";\",\"POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1\",\"]\",\",\",\"point\",\":\",\"usize\",\",\",\"column\",\":\",\"usize\",\",\",\")\",\"-\",\">\",\"QM31\",\"{\",\"claims\",\"[\",\"point\",\"*\",\"POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1\",\"+\",\"column\",\"]\",\"}\"]"
def owned_tokens11_terminal_selected_claim_0 : String := "[\"fn\",\"selected_claim\",\"(\",\"claims\",\":\",\"&\",\"[\",\"QM31\",\";\",\"POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1\",\"]\",\",\",\"point\",\":\",\"usize\",\",\",\"column\",\":\",\"usize\",\",\",\")\",\"-\",\">\",\"QM31\",\"{\",\"claims\",\"[\",\"point\",\"*\",\"POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1\",\"+\",\"column\",\"]\",\"}\"]"
theorem body_identity11_terminal_selected_claim_0 : source_tokens11_terminal_selected_claim_0 = owned_tokens11_terminal_selected_claim_0 :=
  token_identity11 source_tokens11_terminal_selected_claim_0
theorem body_interpretation11_terminal_selected_claim_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_terminal_selected_claim_0 = interpret owned_tokens11_terminal_selected_claim_0 :=
  interpret_identity11 interpret _ _ body_identity11_terminal_selected_claim_0
#print axioms body_identity11_terminal_selected_claim_0
#print axioms body_interpretation11_terminal_selected_claim_0
end PV_B3P_Binding11227
