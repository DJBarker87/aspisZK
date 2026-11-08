import NMX_R4_NMSFold242
import NMX_R4_Authentication
set_option autoImplicit false
noncomputable section
namespace NMX_R4_NMS242Instantiation
/-- Exact NMS canonical consumer, instantiated with the complete233 candidate
and supplied module8. The parent source/carrier gate remains a separate step. -/
theorem fold (choices : NMX_R4_Authentication.Choices) (a : RSL.TX2_242.Args) :
 NMS_R2Refine.Refines
  (NMX_R4_NMSFold242.replay LIBB_PoolLib.library LIBB_PoolLib.deployed
    (NMX_R4_Authentication.authenticate choices) a)
  (RSL.TX2_242.Ref LIBB_PoolLib.library LIBB_PoolLib.deployed a) :=
 NMX_R4_NMSFold242.fold _ _ _ (NMX_R4_Authentication.root choices) a
#print axioms fold
end NMX_R4_NMS242Instantiation
end
