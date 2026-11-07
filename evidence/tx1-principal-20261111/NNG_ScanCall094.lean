import NNG_ParseCall094
import LIBC_CanonicalScan
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ScanCall094
open Aeneas Aeneas.Std Result NMT_tx1

def call (env : RSL.Env) (proof : Slice U8) : Result (core.result.Result Unit verifier.Error) :=
 .ok (if LIBC_CanonicalScan.good (LIB_Carriers.bytes proof) then .Ok () else .Err .Parse)
def port : core.result.Result Unit verifier.Error → Except LIB_VCarriers.VErr Unit
 | .Ok u=>.ok u | .Err e=>.error (NNG_ParseCall094.error e)

theorem graph (env : RSL.Env) (proof : Slice U8) (width : proof.val.length=57607) :
 LIBC_CanonicalScan.child.run (LIB_Carriers.bytes proof) env
  (LIB_Carriers.resultObs port [] (call env proof)) := by
 have domain : LIBC_CanonicalScan.Domain (LIB_Carriers.bytes proof) := by
  change (proof.val.map _).length=57607
  simpa only [List.length_map] using width
 refine ⟨domain,domain,?_⟩
 cases h : LIBC_CanonicalScan.good (LIB_Carriers.bytes proof) <;>
  simp only [call,h,Bool.false_eq_true,if_false,if_true,LIB_Carriers.resultObs,port,
   LIBC_CanonicalScan.value,NNG_ParseCall094.error]
#print axioms graph

/-- Full original native helper result at the original byte slice. -/
theorem source (env : RSL.Env) (proof : Slice U8) (width : proof.val.length=57607) :
 NJS_Extract.verifier.candidate.canonical_scan
  AspisR1M31Parser.field.M31.from_le_bytes NKL_CanonicalInstallation.childK
  NKL_CanonicalInstallation.childE NKL_CanonicalInstallation.childCV proof =
 .ok (NKB_CanonicalOpening.reply (LIBC_CanonicalScan.good (LIB_Carriers.bytes proof))) := by
 have domain : LIBC_CanonicalScan.Domain (LIB_Carriers.bytes proof) := by
  change (proof.val.map _).length=57607
  simpa only [List.length_map] using width
 simpa only [LIBC_Bytes.from_native] using LIBC_CanonicalScan.native_result (LIB_Carriers.bytes proof) domain
#print axioms source
end AspisR1.NNG_ScanCall094
