import NNG_Candidate328
import NNG_P1880Discharge
import LIB_S1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Caller345
open RSL
/-- BOTH328 caller clauses follow from the SAME successful decode/validate
arm. Neither is a new input clause of345, whose Domain remains True. -/
theorem domain (publicData proofData : Bytes) (st : LIB_Instances.C.Statement) (n : Nat)
 (decoded : LIB_Instances.C.decodeStatement publicData=some st)
 (validated : LIB_Instances.C.validateStatement st=true) :
 TX1_328.Domain LIB_Instances.VL
  ⟨LIB_Instances.C.semanticPublic st,publicData,slice proofData AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,n⟩ := by
 constructor
 · exact LIB_S1.validated_public st validated
 · exact TX1_345.p1880_of_decode LIB_Instances.VL LIB_Instances.C
    (NNG_P1880Discharge.decoder LIB_Instances.VL rfl) publicData proofData st decoded n
#print axioms domain
end AspisR1.NNG_Caller345
