import NNH_InstalledImpl
import NNE_RecordSig
import TAS_TopB_NNE
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_G0Partial
open RSL RSL.TAS RSL.TFM RSL.EVB RSL.TASB
open TX2_241 (V2Lib)
open TX1_345 (S1Lib)

/-- CONDITIONAL physical assembly. The base host signature, physical data,
canonical libraries and actual child functions are still installation inputs.
Only missing TAS fields are proof arguments; no PoolLaws, NativeRep, selected,
Root0 or acceptance substitute is added. This is NOT the final host theorem.
A3/A4/A5, dispatch folds and account counts are instantiated below. -/
theorem deployed_splitB_conditional
 (S0 : Sig) (d : NNE_AcceptanceSig.Data S0) (r : NNE_RecordSig.Data S0)
 (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
 (P : PreparedNew VL) (C : S1Lib VL) (I0 : Impl L V0 VL)
 (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (sp : Split (NNE_RecordSig.physical S0 d r))
 (hl : Headline (NNE_RecordSig.physical S0 d r))
 (a0 : A0_Digest (NNE_RecordSig.physical S0 d r))
 (nmm : NMM_Roots L D V0 VL (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (nmx : NMX_Root L D V0 VL (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (nms : NMS_Roots L D V0 VL (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (nmv : NMV_Roots L D V0 VL P C (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (nmt : NMT_Roots L V0 VL P C (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (nmp : NMP_Roots L V0 VL P (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (nmo : NMO_Root L V0 VL (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (nmn : NMN_Root L V0 VL (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (g1a : NNC_G1a (NNE_RecordSig.physical S0 d r) L V0 VL
   (NNH_InstalledImpl.install I0 alloc1 alloc2))
 (R : RecSig (NNE_RecordSig.physical S0 d r))
 (rs : RecSelect (NNE_RecordSig.physical S0 d r) R)
 (hb : HeadlineB (NNE_RecordSig.physical S0 d r) R)
 (nmfB : NNC_NMFPrimeB (NNE_RecordSig.physical S0 d r) L D V0 VL P C
   (NNH_InstalledImpl.install I0 alloc1 alloc2) g1a R)
 (r0 : NNC_R0Rep (NNE_RecordSig.physical S0 d r) V0)
 (a1 : NND_A1 (NNE_RecordSig.physical S0 d r) VL P C)
 (a2 : NND_A2 (NNE_RecordSig.physical S0 d r) L D V0)
 (X : ExecB (NNE_RecordSig.physical S0 d r) R)
 (fx : X.Fixed) (w : X.World) (H : X.Oracle)
 (queries : X.QueriesF fx)
 (run : Runs (NNE_RecordSig.physical S0 d r)
   (NNH_InstalledImpl.install I0 alloc1 alloc2) (ctxB X fx w H)) :
 (NNE_RecordSig.physical S0 d r).Bound (ctxB X fx w H)
   (S0.model1 (ctxB X fx w H)) (S0.model2 (ctxB X fx w H)) ∧
 sp.Rest (ctxB X fx w H) (S0.model1 (ctxB X fx w H)) (S0.model2 (ctxB X fx w H)) ∧
 (hb.OutcomeRec (ctxB X fx w H) (S0.model1 (ctxB X fx w H)) (S0.model2 (ctxB X fx w H)) ∨
   X.ERec fx H) := by
 let S := NNE_RecordSig.physical S0 d r
 let I := NNH_InstalledImpl.install I0 alloc1 alloc2
 exact top_splitB_physical L D V0 VL P C I sp hl a0 nmm nmx nms nmv
   (NNH_InstalledImpl.dispatch L D V0 VL P C I0 alloc1 alloc2) nmt nmp nmo nmn
   g1a rs hb nmfB r0 a1 a2
   (NNE_RecordSig.a3 S0 d r VL P C) (NNE_RecordSig.a4 S0 d r L D V0)
   (NNE_RecordSig.a5 S0 d r L V0 VL P C I)
   (fun c => NNE_EntryArgs.count (d.e1 c) 3 (d.program c) (d.data1 c))
   (fun c => NNE_EntryArgs.count (d.e2 c) 7 (d.program c) (d.data2 c))
   X fx w H queries run

#print axioms deployed_splitB_conditional
end AspisR1.NNH_G0Partial
