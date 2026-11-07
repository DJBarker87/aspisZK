import NNH_TasRoots
set_option autoImplicit false
namespace NNH_CandidateRoots
open RSL

/-- Full interpreted source-fission root under ruling (bn). The reviewed
transcription and native cut receipts are external certificate evidence;
this theorem adds no native-producer or endpoint hypothesis. -/
theorem root344 (V : VLib) (P : PreparedNew V) (C : TX1_345.S1Lib V)
 (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX1_345.Args → Env → Obs (Except ProgramError Bytes))
 (packet : TX1_345.RowSpec_345 V P C child) :
 TX1_344.RowSpec_344 V P C (NMV_ConcreteWindows.stage1 allocation child) :=
 NMV_ConcreteWindows.root344 V P C allocation child packet

/-- EVERY verifier library, including the weak library, at the SAME child. -/
theorem root240 (L : PoolLib) (D : DeployedIds) (V : TX2_241.V2Lib)
 (allocation : NMV_ConcreteWindows.Allocation)
 (child : TX2_241.Args → Env → Obs (Except ProgramError Unit))
 (packet : TX2_241.RowSpec_241 L D V child) :
 TX2_240.RowSpec_240 L D V (NMV_ConcreteWindows.stage2 allocation child) :=
 NMV_ConcreteWindows.root240 L D V allocation child packet

/-- Exact TAS fields, preserving the original child constants. PoolLaws is
an explicit library installation boundary, not a wrapper own-input clause. -/
def packet (L : PoolLib) (D : DeployedIds) (V0 : TX2_241.V2Lib) (VL : VLib)
 (P : PreparedNew VL) (C : TX1_345.S1Lib VL)
 (I : TAS.Impl L V0 VL) (a1 a2 : NMV_ConcreteWindows.Allocation)
 (pl : NMV_NoWrite.PoolLaws L) :
 TAS.NMV_Roots L D V0 VL P C (NNH_TasRoots.implementation I a1 a2) :=
 NNH_TasRoots.packet L D V0 VL P C I a1 a2 pl

#print axioms root344
#print axioms root240
#print axioms packet
end NNH_CandidateRoots
