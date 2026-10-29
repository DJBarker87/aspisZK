import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- poseidon/pow5#0; complete source and owned lexical token sequences. -/
def source_tokens11_poseidon_pow5_0 : String := "[\"fn\",\"pow5\",\"(\",\"value\",\":\",\"QM31\",\")\",\"-\",\">\",\"QM31\",\"{\",\"let\",\"square\",\"=\",\"value\",\".\",\"square\",\"(\",\")\",\";\",\"square\",\".\",\"square\",\"(\",\")\",\".\",\"mul\",\"(\",\"value\",\")\",\"}\"]"
def owned_tokens11_poseidon_pow5_0 : String := "[\"fn\",\"pow5\",\"(\",\"value\",\":\",\"QM31\",\")\",\"-\",\">\",\"QM31\",\"{\",\"let\",\"square\",\"=\",\"value\",\".\",\"square\",\"(\",\")\",\";\",\"square\",\".\",\"square\",\"(\",\")\",\".\",\"mul\",\"(\",\"value\",\")\",\"}\"]"
theorem body_identity11_poseidon_pow5_0 : source_tokens11_poseidon_pow5_0 = owned_tokens11_poseidon_pow5_0 :=
  token_identity11 source_tokens11_poseidon_pow5_0
theorem body_interpretation11_poseidon_pow5_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_poseidon_pow5_0 = interpret owned_tokens11_poseidon_pow5_0 :=
  interpret_identity11 interpret _ _ body_identity11_poseidon_pow5_0
#print axioms body_identity11_poseidon_pow5_0
#print axioms body_interpretation11_poseidon_pow5_0
end PV_B3P_Binding11227
