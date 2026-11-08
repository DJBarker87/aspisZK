import NNV_CurrentScan
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_ScanWeakErr
open Aeneas Aeneas.Std Result NNH_Run5bCurrentShape
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
theorem accepted (proof : Slice U8) (width : proof.val.length=57607)
 (called : (current m env err r).op4 proof = .ok (.Ok ())) :
 LIB_VLib.canonicalScanValue (LIB_Carriers.bytes proof) env = .ok () := by
 rw [NNV_CurrentScan.source m env err r proof width] at called
 change LIBC_CanonicalScan.value _ env = .ok ()
 unfold LIBC_CanonicalScan.value
 split at called
 · rename_i good
   rw [if_pos good]
 · cases called

theorem rejected (proof : Slice U8) (width : proof.val.length=57607)
 (e : LIB_VCarriers.VErr)
 (returned : LIB_VLib.canonicalScanValue (LIB_Carriers.bytes proof) env = .error e) :
 (current m env err r).op4 proof ≠ .ok (.Ok ()) := by
 intro called
 have value := accepted m env err r proof width called
 rw [returned] at value
 cases value
#print axioms accepted
#print axioms rejected
end AspisR1.NNV_ScanWeakErr
end
