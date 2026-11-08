import NNH_Run5bCurrentShape
import LIBC_CanonicalScan
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CurrentScan
open Aeneas Aeneas.Std Result NNH_Run5bCurrentShape
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
theorem slot (proof : Slice U8) :
 (current m env err r).op4 proof = Op4P_Install.sourceBody proof := rfl

theorem source (proof : Slice U8) (width : proof.val.length=57607) :
 (current m env err r).op4 proof =
 .ok (if LIBC_CanonicalScan.good (LIB_Carriers.bytes proof) then .Ok () else .Err .Parse) := by
 have raw : LIBC_Bytes.raw (LIB_Carriers.bytes proof) = proof := LIBC_Bytes.from_native proof
 have meaning := NKL_ScanModel.value proof width
 change LIBC_CanonicalScan.good (LIB_Carriers.bytes proof) = _ at meaning
 rw [slot,Op4P_Install.sourceBody,Op4P_Refinement.reference_total proof width]
 unfold LIBC_CanonicalScan.good
 rw [raw,meaning]
 split <;> simp_all only [decide_true,decide_false,bind_tc_ok,if_true,if_false,Bool.false_eq_true]

theorem returned (proof : Slice U8) (width : proof.val.length=57607)
 (called : LIB_VLib.canonicalScanValue (LIB_Carriers.bytes proof) env = .ok ()) :
 (current m env err r).op4 proof = .ok (.Ok ()) := by
 have good : LIBC_CanonicalScan.good (LIB_Carriers.bytes proof)=true := by
  change LIBC_CanonicalScan.value _ env = .ok () at called
  unfold LIBC_CanonicalScan.value at called
  split at called
  · assumption
  · cases called
 rw [source m env err r proof width,good]
 rfl
#print axioms slot
#print axioms source
#print axioms returned
end AspisR1.NNV_CurrentScan
end
