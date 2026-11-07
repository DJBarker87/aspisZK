import LIBB_PoolScan
import LIBB_NoWriteGraph
set_option autoImplicit false
noncomputable section
namespace LIBB_ScanNoWrite
open Aeneas Aeneas.Std
open RSL NMV_NoWrite LIBB_NoWriteGraph
/-- Only the literal scanner control is opened. The codecs stay symbolic. -/
theorem source (bytes : Slice U8) : Free (NMS_R2N_ScanSites.interpreted bytes) := by
 unfold NMS_R2N_ScanSites.interpreted NMS_R2N_ScanSites.scan
 apply bind_free _ _ (LIBB_NoWriteGraph.lift _)
 intro expected
 cases expected with
 | none => exact LIBB_NoWriteGraph.lift _
 | some size =>
   dsimp only
   split
   · exact LIBB_NoWriteGraph.lift _
   · apply bind_free _ _ (LIBB_NoWriteGraph.lift _)
     intro header
     apply bind_free _ _ (LIBB_NoWriteGraph.lift _)
     intro decoded
     cases decoded with
     | Err error => exact LIBB_NoWriteGraph.lift _
     | Ok candidate =>
       dsimp only
       apply bind_free _ _ alloc_free
       intro unit
       apply bind_free _ _ (LIBB_NoWriteGraph.lift _)
       intro encoded
       cases encoded with
       | Err error => exact LIBB_NoWriteGraph.lift _
       | Ok encoded =>
         dsimp only
         split
         · exact LIBB_NoWriteGraph.lift _
         · apply bind_free _ _ (LIBB_NoWriteGraph.lift _)
           intro tag
           split <;> exact LIBB_NoWriteGraph.lift _

theorem scan (data : Bytes) : Free (LIBB_PoolScan.scanProof data) := by
 unfold LIBB_PoolScan.scanProof
 split
 · exact LIBB_NoWriteGraph.map _ _ (source _)
 · exact panic_free
#print axioms source
#print axioms scan
end LIBB_ScanNoWrite
end
