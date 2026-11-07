import LIB_Instances
import LIBB_PoolLib
import LIBB_V2Star
set_option autoImplicit false
noncomputable section
namespace LIB_FullInstances
open RSL
abbrev L : PoolLib := LIBB_PoolLib.library
abbrev V0 : TX2_241.V2Lib := LIBB_V2Star.library
abbrev VL := LIB_Instances.VL
abbrev P := LIB_Instances.P
abbrev C := LIB_Instances.C
abbrev D := LIB_Instances.D
structure Bundle where
 pool : PoolLib
 deployed : DeployedIds
 verifier0 : TX2_241.V2Lib
 verifier1 : VLib
 prepared : PreparedNew verifier1
 statement : TX1_345.S1Lib verifier1
def library : Bundle := ⟨L,D,V0,VL,P,C⟩
theorem pool_exact : library.pool = LIBB_PoolLib.library := rfl
theorem v0_exact : library.verifier0 = LIBB_V2Star.library := rfl
theorem vl_exact : library.verifier1 = LIB_Instances.VL := rfl
theorem deployed_exact : library.deployed = LIB_Deployed.deployed := rfl
theorem prepared_exact : library.prepared = LIB_Instances.P := rfl
theorem statement_exact : library.statement = LIB_Instances.C := rfl
theorem canonical : TAS.lib V0 V0.Root0 V0.tx2auth = V0 := rfl
abbrev weak := @LIBB_V2Star.weak
section TASChecks
open LIB_Instances (resultType)
variable (I : TAS.Impl L V0 VL)
theorem tas217 : TX2_217.RowSpec_217 I.f217 =
 resultType (fun r : TAS.NMM_Roots L D V0 VL I => r.r217) := rfl
theorem tas234 : TX2_234.RowSpec_234 L D I.f234 =
 resultType (fun r : TAS.NMM_Roots L D V0 VL I => r.r234) := rfl
theorem tas233 : (TX2_234.RowSpec_234 L D I.f234 → TX2_217.RowSpec_217 I.f217 →
 TX2_233.RowSpec_233 L D I.f233) =
 resultType (fun r : TAS.NMX_Root L D V0 VL I => r.r233) := rfl
theorem tas242 : (TX2_233.RowSpec_233 L D I.f233 → TX2_242.RowSpec_242 L D I.f242) =
 resultType (fun r : TAS.NMS_Roots L D V0 VL I => r.r242) := rfl
theorem tas064 : TAS.Refines064 V0 I.f064 V0.Root0 V0.tx2auth =
 resultType (fun r : TAS.NMN_Root L V0 VL I => r.r064) := rfl
theorem tas241 : (∀ (R0 : Bytes → Bytes → Prop)
 (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)),
 TAS.Refines064 V0 I.f064 R0 w → TX2_242.RowSpec_242 L D I.f242 →
 TX2_241.RowSpec_241 L D (TAS.lib V0 R0 w) I.f241) =
 resultType (fun r : TAS.NMS_Roots L D V0 VL I => r.r241) := rfl
theorem tas240 : (∀ V : TX2_241.V2Lib,
 TX2_241.RowSpec_241 L D V I.f241 → TX2_240.RowSpec_240 L D V I.f240) =
 resultType (fun r : TAS.NMV_Roots L D V0 VL P C I => r.r240) := rfl
theorem tas221 : (∀ V : TX2_241.V2Lib, TX1_344.RowSpec_344 VL P C I.f344 →
 TX2_240.RowSpec_240 L D V I.f240 →
 TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) I.process) =
 resultType (fun r : TAS.NMW_Roots L D V0 VL P C I => r.r221) := rfl
theorem tas213 : (∀ V : TX2_241.V2Lib,
 TX2_221.RowSpec_221 L D V (TX1_344.asStage1 VL P C) I.process →
 TX2_213.RowSpec_213 L D V (TX1_344.asStage1 VL P C) I.entry) =
 resultType (fun r : TAS.NMW_Roots L D V0 VL P C I => r.r213) := rfl
end TASChecks
#print axioms pool_exact
#print axioms v0_exact
#print axioms vl_exact
#print axioms deployed_exact
#print axioms prepared_exact
#print axioms statement_exact
#print axioms canonical
#print axioms tas217
#print axioms tas234
#print axioms tas233
#print axioms tas242
#print axioms tas064
#print axioms tas241
#print axioms tas240
#print axioms tas221
#print axioms tas213
end LIB_FullInstances
