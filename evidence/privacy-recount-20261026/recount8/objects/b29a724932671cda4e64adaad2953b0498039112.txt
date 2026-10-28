import R1Z.BuilderForestAdmissionPort
import R0Z.PoseidonExtracted

/-! Exact frozen table association. Only the literal arrays are compared;
no permutation, recurrence or large finite carrier is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceTables

theorem initial : BuilderForestAdmissionPort.poseidon2.EXTERNAL_INITIAL =
    R0PoseidonCopy.EXTERNAL_INITIAL := by
  simp only [BuilderForestAdmissionPort.poseidon2.EXTERNAL_INITIAL,R0PoseidonCopy.EXTERNAL_INITIAL]

theorem internal : BuilderForestAdmissionPort.poseidon2.INTERNAL =
    R0PoseidonCopy.INTERNAL := by
  simp only [BuilderForestAdmissionPort.poseidon2.INTERNAL,R0PoseidonCopy.INTERNAL]

theorem final_constants : BuilderForestAdmissionPort.poseidon2.EXTERNAL_FINAL =
    R0PoseidonCopy.EXTERNAL_FINAL := by
  simp only [BuilderForestAdmissionPort.poseidon2.EXTERNAL_FINAL,R0PoseidonCopy.EXTERNAL_FINAL]

#print axioms initial
#print axioms internal
#print axioms final_constants
end R1Z.PV_RunJoin_SourceTables
