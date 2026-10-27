import R1Z.PV_Canon_Inverse
import R1Z.ProverRwSuccessInverseInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
/-- Range preservation must not turn the zero assertion into field inversion.
This local return equation does not prove witness-independence of zero events. -/
theorem owned_inverse_zero : ProverCommitInverse48.inverse_owned 0#u32 = .fail .panic := by
  rw [ProverCommitInverse48.inverse_result]
  rfl
 theorem scalar_try_inverse_zero : ProverRwSuccessInverseInstall.Src.mInv 0#u32 = .ok none := by
  rfl
#print axioms owned_inverse_zero
#print axioms scalar_try_inverse_zero
end R1Z.PV_Canon
