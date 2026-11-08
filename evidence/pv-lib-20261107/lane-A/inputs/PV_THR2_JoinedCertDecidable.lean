import PV_THR2_JoinedCertDescriptor
set_option autoImplicit false
namespace PV_THR2_JoinedCertDecidable
open PV_STX2_Syntax
/-- Transparent structural decision procedure for finite descriptor tests.
This adds no proposition or hypothesis; generated tests remain small syntax. -/
instance extra (fn : Data) : Decidable (PV_THR2_JoinedCertDescriptor.Extra fn) := by
  unfold PV_THR2_JoinedCertDescriptor.Extra
  infer_instance
#print axioms extra
end PV_THR2_JoinedCertDecidable
