import NMX_R6_Observation
import NMS_R2N_ScanSites
set_option autoImplicit false
noncomputable section
namespace NMX_R6_ScanComplete
open Aeneas Aeneas.Std Result
open NMX_R6_Observation
local instance : MonadLift Result Result where
 monadLift := id
/-- Source value preservation with allocation at its actual source point. -/
theorem complete (bytes : Slice U8) :
 Complete (NMS_R2N_ScanSites.interpreted bytes)
  (NMS_R2N_ScanSites.scan (M := Result) (ok ()) bytes) := by
 unfold NMS_R2N_ScanSites.interpreted NMS_R2N_ScanSites.scan
 apply NMX_R6_Observation.complete_bind _ _ _ _ (NMX_R6_Observation.lift _)
 intro expected
 cases expected with
 | none => exact NMX_R6_Observation.lift _
 | some size =>
   dsimp only
   apply NMX_R6_Observation.branch
   · exact NMX_R6_Observation.lift _
   · apply NMX_R6_Observation.complete_bind _ _ _ _ (NMX_R6_Observation.lift _)
     intro header
     apply NMX_R6_Observation.complete_bind _ _ _ _ (NMX_R6_Observation.lift _)
     intro decoded
     cases decoded with
     | Err error => exact NMX_R6_Observation.lift _
     | Ok candidate =>
       dsimp only
       apply NMX_R6_Observation.complete_bind _ _ _ _ NMX_R6_Observation.allocate
       intro unit
       apply NMX_R6_Observation.complete_bind _ _ _ _ (NMX_R6_Observation.lift _)
       intro encoded
       cases encoded with
       | Err error => exact NMX_R6_Observation.lift _
       | Ok encoded =>
         dsimp only
         apply NMX_R6_Observation.branch
         · exact NMX_R6_Observation.lift _
         · apply NMX_R6_Observation.complete_bind _ _ _ _ (NMX_R6_Observation.lift _)
           intro tag
           apply NMX_R6_Observation.branch
           · exact NMX_R6_Observation.lift _
           · exact NMX_R6_Observation.lift _

#print axioms complete
end NMX_R6_ScanComplete
end
