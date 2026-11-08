import LIBW_WeakPerEnv
import NNH_064WeakField
set_option autoImplicit false
noncomputable section
namespace NNP_HostIdentity
open AspisR1

theorem host_law : LIBW_WeakPerEnv.wEnv NNH_064Install.frame = NNH_064WeakField.w := rfl

theorem host_library : LIBW_WeakPerEnv.weakEnv NNH_064Install.frame =
 RSL.TCK.weaken NNH_Libraries.V0 NNH_064WeakField.w := rfl

/-- Reuse the merged concrete host refinement; no HostRep premise is added. -/
theorem host_refines : RSL.TAS.Refines064 LIBB_V2Star.library NNH_064Install.f064
 (fun _ _ => True) (LIBW_WeakPerEnv.wEnv NNH_064Install.frame) :=
 NNH_064WeakField.weak

theorem host_refines_any : RSL.TAS.Refines064 LIBB_V2Star.library NNH_064Install.f064
 (fun _ _ => True) (LIBW_WeakPerEnv.wAny Unit) :=
 LIBW_WeakPerEnv.refines_any NNH_064Install.frame NNH_064Install.f064 host_refines

#print axioms host_law
#print axioms host_library
#print axioms host_refines
#print axioms host_refines_any
end NNP_HostIdentity
