import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- copy/pattern_values#0; complete source and owned lexical token sequences. -/
def source_tokens11_copy_pattern_values_0 : String := "[\"fn\",\"pattern_values\",\"(\",\"openings\",\":\",\"&\",\"[\",\"QM31\",\";\",\"POSEIDON2_WIDTH\",\"]\",\",\",\"lambda\",\":\",\"QM31\",\",\",\")\",\"-\",\">\",\"[\",\"QM31\",\";\",\"POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1\",\"]\",\"{\",\"#\",\"[\",\"cfg\",\"(\",\"not\",\"(\",\"feature\",\"=\",\"\\\"optimized-terminal\\\"\",\")\",\")\",\"]\",\"return\",\"pattern_values_literal\",\"(\",\"openings\",\",\",\"lambda\",\")\",\";\",\"#\",\"[\",\"cfg\",\"(\",\"feature\",\"=\",\"\\\"optimized-terminal\\\"\",\")\",\"]\",\"return\",\"pattern_values_windowed\",\"(\",\"openings\",\",\",\"lambda\",\")\",\";\",\"}\"]"
def owned_tokens11_copy_pattern_values_0 : String := "[\"fn\",\"pattern_values\",\"(\",\"openings\",\":\",\"&\",\"[\",\"QM31\",\";\",\"POSEIDON2_WIDTH\",\"]\",\",\",\"lambda\",\":\",\"QM31\",\",\",\")\",\"-\",\">\",\"[\",\"QM31\",\";\",\"POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1\",\"]\",\"{\",\"#\",\"[\",\"cfg\",\"(\",\"not\",\"(\",\"feature\",\"=\",\"\\\"optimized-terminal\\\"\",\")\",\")\",\"]\",\"return\",\"pattern_values_literal\",\"(\",\"openings\",\",\",\"lambda\",\")\",\";\",\"#\",\"[\",\"cfg\",\"(\",\"feature\",\"=\",\"\\\"optimized-terminal\\\"\",\")\",\"]\",\"return\",\"pattern_values_windowed\",\"(\",\"openings\",\",\",\"lambda\",\")\",\";\",\"}\"]"
theorem body_identity11_copy_pattern_values_0 : source_tokens11_copy_pattern_values_0 = owned_tokens11_copy_pattern_values_0 :=
  token_identity11 source_tokens11_copy_pattern_values_0
theorem body_interpretation11_copy_pattern_values_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_copy_pattern_values_0 = interpret owned_tokens11_copy_pattern_values_0 :=
  interpret_identity11 interpret _ _ body_identity11_copy_pattern_values_0
#print axioms body_identity11_copy_pattern_values_0
#print axioms body_interpretation11_copy_pattern_values_0
end PV_B3P_Binding11227
