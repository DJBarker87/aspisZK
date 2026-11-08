import NMX_R9_StageTwo
import TAS_Interfaces
set_option autoImplicit false
noncomputable section
namespace NNS_Fold241
open RSL RSL.TX2_241 NMS_R2Replay241
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed
abbrev V0 := LIBB_V2Star.library

/-- Exact TAS premise supplies the original NMS packet on the SAME library.
This changes no domain and adds no Root0 premise. -/
theorem packet (f : Bytes → Bytes → Bytes → Env → Obs (Except V0.VErr Unit))
 (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (h : TAS.Refines064 V0 f R0 w) :
 VerifyPacket (TAS.lib V0 R0 w) (fun x env => f x.1 x.2.1 x.2.2 env) := h

/-- Parametric deterministic replay support, NOT the credited stage2.
The missing source selection association is deliberately not assumed here. -/
theorem fold (ch : NMX_R4_Authentication.Choices)
 (f : Bytes → Bytes → Bytes → Env → Obs (Except V0.VErr Unit))
 (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (h064 : TAS.Refines064 V0 f R0 w)
 (h242 : TX2_242.RowSpec_242 L D (NMX_R6_Validation.validate ch))
 (a : Args) (domain : Domain (TAS.lib V0 R0 w) a) :
 NMS_R2Refine.Refines
  (replay L (TAS.lib V0 R0 w) (NMX_R6_Validation.validate ch)
   (fun x env => f x.1 x.2.1 x.2.2 env) a)
  (TX2_241.Ref L D (TAS.lib V0 R0 w) a) :=
 NMS_R2Fold241.fold L D _ _ h242 LIBB_ScannerExtent.extent _
  (packet f R0 w h064) a domain

#print axioms packet
#print axioms fold
end NNS_Fold241
