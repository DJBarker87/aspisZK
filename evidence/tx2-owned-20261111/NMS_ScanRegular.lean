import NMS_ScanSites
import NMS_RegularControl
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
   dsimp only
   apply NMS_RegularControl.branch
   · exact NMS_Regular.lift _
   · apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
     intro header
     apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
     intro decoded
     cases decoded with
     | Err error => exact NMS_Regular.lift _
     | Ok candidate =>
       dsimp only
       apply NMS_AllocationRegular.bind
       apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
       intro encoded
       cases encoded with
       | Err error => exact NMS_Regular.lift _
       | Ok encoded =>
         dsimp only
         apply NMS_RegularControl.branch
         · exact NMS_Regular.lift _
         · apply NMS_Regular.bind _ _ _ _ (NMS_Regular.lift _)
           intro tag
           apply NMS_RegularControl.branch
           · exact NMS_Regular.lift _
           · exact NMS_Regular.lift _

theorem source_return (bytes : Slice U8) (env : RSL.Env)
 (reply : core.result.Result AdapterRw.r1_pool_adapter.ScannedAsqaProof AdapterRw.solana_program_error.ProgramError)
 (events : List RSL.Event) (run : NMS_ScanSites.interpreted bytes env ⟨.ret reply,events⟩) :
 AspisR1.NFY_JHf_Scan.source bytes = .ok reply := by
 rw [←NMS_ScanSites.erases]
 exact regular bytes env reply events run

#print axioms regular
#print axioms source_return
end NMS_ScanRegular
