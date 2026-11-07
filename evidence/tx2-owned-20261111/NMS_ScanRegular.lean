import NMS_ScanSites
import NMS_Regular
set_option autoImplicit false
noncomputable section
namespace NMS_ScanRegular
open Aeneas Aeneas.Std Result
open NMS_Regular
local instance : MonadLift Result Result where
 monadLift := id
/-- Source value preservation with allocation at its actual source point. -/
theorem regular (bytes : Slice U8) :
 Law (NMS_ScanSites.interpreted bytes)
  (NMS_ScanSites.scan (M := Result) (ok ()) bytes) := by
 unfold NMS_ScanSites.interpreted NMS_ScanSites.scan
 apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
 intro expected
 cases expected with
 | none => exact NMS_Regular.lift _
 | some size =>
   cases guard : (Slice.len bytes != size) with
   | true => exact NMS_Regular.lift _
   | false =>
     apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
     intro header
     apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
     intro decoded
     cases decoded with
     | Err error => exact NMS_Regular.lift _
     | Ok candidate =>
       apply NMS_Regular.bind _ _ _ _ NMS_Regular.allocate
       intro unit
       cases unit
       apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
       intro encoded
       cases encoded with
       | Err error => exact NMS_Regular.lift _
       | Ok encoded =>
         cases guard : (encoded.val != header.val) with
         | true => exact NMS_Regular.lift _
         | false =>
           apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
           intro tag
           cases guard : (tag != 2#u8) with
           | true => exact NMS_Regular.lift _
           | false => exact NMS_Regular.lift _

theorem source_return (bytes : Slice U8) (env : RSL.Env)
 (reply : core.result.Result AdapterRw.r1_pool_adapter.ScannedAsqaProof AdapterRw.solana_program_error.ProgramError)
 (events : List RSL.Event) (run : NMS_ScanSites.interpreted bytes env ⟨.ret reply,events⟩) :
 AspisR1.NFY_JHf_Scan.source bytes = .ok reply := by
 rw [←NMS_ScanSites.erases]
 exact regular bytes env reply events run

#print axioms regular
#print axioms source_return
end NMS_ScanRegular
