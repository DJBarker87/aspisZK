import NMX_R7_Verify241
import NMX_R6_Validation
import LIBB_ScannerExtent
set_option autoImplicit false
noncomputable section
namespace NMX_R7_Fold241
open RSL
/-- Fixed NMS consumer with242 and064 installed. D1/D2 are exactly the
original241 Domain. Scanner extent and entered064 clauses are derived by the
NMS fold at SAME reads; no new own-input or successful-child clause. -/
theorem fold (choices : NMX_R4_Authentication.Choices) (a : TX2_241.Args)
 (domain : TX2_241.Domain LIBB_V2Star.library a) :
 NMS_R2Refine.Refines
  (NMS_R2Replay241.replay LIBB_PoolLib.library LIBB_V2Star.library
   (NMX_R6_Validation.validate choices) NMX_R7_Verify241.verify a)
  (TX2_241.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library a) := by
 apply NMS_R2Fold241.fold _ _ _ _ (NMX_R6_Validation.root choices)
 · exact LIBB_ScannerExtent.extent
 · exact NMX_R7_Verify241.packet
 · exact domain
#print axioms fold
end NMX_R7_Fold241
end
