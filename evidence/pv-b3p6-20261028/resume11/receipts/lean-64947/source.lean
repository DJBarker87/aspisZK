import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- poseidon/internal_round#0; complete source and owned lexical token sequences. -/
def source_tokens11_poseidon_internal_round_0 : String := "[\"fn\",\"internal_round\",\"(\",\"mut\",\"state\",\":\",\"[\",\"QM31\",\";\",\"POSEIDON2_WIDTH\",\"]\",\",\",\"constant\",\":\",\"QM31\",\")\",\"-\",\">\",\"[\",\"QM31\",\";\",\"16\",\"]\",\"{\",\"state\",\"[\",\"0\",\"]\",\"=\",\"pow5\",\"(\",\"state\",\"[\",\"0\",\"]\",\".\",\"add\",\"(\",\"constant\",\")\",\")\",\";\",\"internal_linear_lazy\",\"(\",\"&\",\"mut\",\"state\",\")\",\";\",\"state\",\"}\"]"
def owned_tokens11_poseidon_internal_round_0 : String := "[\"fn\",\"internal_round\",\"(\",\"mut\",\"state\",\":\",\"[\",\"QM31\",\";\",\"POSEIDON2_WIDTH\",\"]\",\",\",\"constant\",\":\",\"QM31\",\")\",\"-\",\">\",\"[\",\"QM31\",\";\",\"16\",\"]\",\"{\",\"state\",\"[\",\"0\",\"]\",\"=\",\"pow5\",\"(\",\"state\",\"[\",\"0\",\"]\",\".\",\"add\",\"(\",\"constant\",\")\",\")\",\";\",\"internal_linear_lazy\",\"(\",\"&\",\"mut\",\"state\",\")\",\";\",\"state\",\"}\"]"
theorem body_identity11_poseidon_internal_round_0 : source_tokens11_poseidon_internal_round_0 = owned_tokens11_poseidon_internal_round_0 :=
  token_identity11 source_tokens11_poseidon_internal_round_0
theorem body_interpretation11_poseidon_internal_round_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_poseidon_internal_round_0 = interpret owned_tokens11_poseidon_internal_round_0 :=
  interpret_identity11 interpret _ _ body_identity11_poseidon_internal_round_0
#print axioms body_identity11_poseidon_internal_round_0
#print axioms body_interpretation11_poseidon_internal_round_0
end PV_B3P_Binding11227
