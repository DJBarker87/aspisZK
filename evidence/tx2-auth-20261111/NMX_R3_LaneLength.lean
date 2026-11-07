import RSL_TX2_217
set_option autoImplicit false
namespace NMX_R3_LaneLength
open RSL
/-- The first source test rejects every nonmatching length, before any read,
digest invocation or allocation. No caller extent premise is introduced. -/
theorem reference (b : Bytes) (wrong : b.length ≠ LANE_ACCOUNT_BYTES) :
    TX2_217.Ref b = RS.throw .invalidAccountData := by
  have header : TX2_217.headerBad b = true := by
    simp only [TX2_217.headerBad,
      show (b.length != LANE_ACCOUNT_BYTES) = true by simp [wrong], Bool.true_or]
  simp only [TX2_217.Ref, TX2_217.laneDecode, header, ↓reduceIte]

/-- Exact full observation, including the empty event prefix. -/
theorem observation (b : Bytes) (wrong : b.length ≠ LANE_ACCOUNT_BYTES)
    (env : Env) (o : Obs (Except ProgramError LaneState)) :
    TX2_217.Ref b env o ↔ o = ⟨.ret (.error .invalidAccountData), []⟩ := by
  rw [reference b wrong]
  rfl
#print axioms reference
#print axioms observation
end NMX_R3_LaneLength
