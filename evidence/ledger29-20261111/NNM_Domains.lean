import NNG_ActualCandidate345
import NNG_Candidate344
import NMX_R4_Authentication
import NMX_R6_Validation
import NMX_R9_StageTwo
import LIB_FullInstances
set_option autoImplicit false
noncomputable section
namespace NNM_Domains
open AspisR1

theorem exact345 : RSL.TX1_345.RowSpec_345 LIB_FullInstances.VL LIB_FullInstances.P LIB_FullInstances.C
 NNG_TotalProducer345.producer := NNG_ActualCandidate345.candidate

theorem exact344 : RSL.TX1_344.RowSpec_344 LIB_FullInstances.VL LIB_FullInstances.P LIB_FullInstances.C
 NNG_Candidate344.producer := NNG_Candidate344.candidate

theorem exact233 (c : NMX_R4_Authentication.Choices) : RSL.TX2_233.RowSpec_233
 LIBB_PoolLib.library LIBB_PoolLib.deployed (NMX_R4_Authentication.authenticate c) := NMX_R4_Authentication.root c

theorem exact242 (c : NMX_R4_Authentication.Choices) : RSL.TX2_242.RowSpec_242
 LIBB_PoolLib.library LIBB_PoolLib.deployed (NMX_R6_Validation.validate c) := NMX_R6_Validation.root c

theorem exact241 (c : NMX_R4_Authentication.Choices) : RSL.TX2_241.RowSpec_241
 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library (NMX_R9_StageTwo.stage2 c) := NMX_R9_StageTwo.root c

theorem domain345 (a : RSL.TX1_345.Args) : RSL.TX1_345.Domain a = True := rfl
theorem domain344 (a : RSL.TX1_344.Args) (s : RSL.SdkState) : RSL.TX1_344.Domain a s = True := rfl
theorem domain233 (a : RSL.TX2_233.Args) : RSL.TX2_233.Domain a = True := rfl
theorem domain242 (a : RSL.TX2_242.Args) : RSL.TX2_242.Domain a = True := rfl
#print axioms exact345
#print axioms exact344
#print axioms exact233
#print axioms exact242
#print axioms exact241
#print axioms domain345
#print axioms domain344
#print axioms domain233
#print axioms domain242
end NNM_Domains
