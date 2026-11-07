import NNH_064Install
import NNH_LeafInstall
import NNH_LibraryStages
import NNH_HostEnv
import LIB_Deployed
import NNH_InstalledImpl
import NNE_RecordSig
import TAS_TopB_NNE
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_G0With064
open RSL RSL.TAS RSL.TFM RSL.EVB RSL.TASB
open TX2_241 (V2Lib)
open TX1_345 (S1Lib)
open NNH_Libraries

/-- CONDITIONAL assembly with concrete library, total computed064, and published136/217 producers.
The136 native gate is credited by NNI_. The217 native gate is open;
its mathematical candidate remains separate from native credit. Integration gives no row credit. The base host signature, physical data,
actual child functions are still installation inputs. The canonical library
bundles and stage/G2 fields are installed concretely.
Only missing TAS fields are proof arguments; no PoolLaws, NativeRep, selected,
Root0 or acceptance substitute is added. This is NOT the final host theorem.
A3/A4/A5, dispatch folds and account counts are instantiated below. -/
theorem deployed_splitB_conditional
 (Sbase : Sig) (runtime : NNH_HostEnv.Runtime Sbase.Ctx) (d : NNE_AcceptanceSig.Data (NNH_HostEnv.install Sbase runtime)) (r : NNE_RecordSig.Data (NNH_HostEnv.install Sbase runtime))
 (I0 : Impl L V0 VL) (allocation217 : Bytes → Env → Bool)
 (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (sp : Split (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r))
 (hl : Headline (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r))
 (a0 : A0_Digest (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r))
 (registry : TX2_234.RowSpec_234 L D I0.f234)
 (nmx : NMX_Root L LIB_Deployed.deployed V0 VL (NNH_InstalledImpl.install (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2))
 (nms : NMS_Roots L LIB_Deployed.deployed V0 VL (NNH_InstalledImpl.install (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2))
 (nmt : NMT_Roots L V0 VL P C (NNH_InstalledImpl.install (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2))
 (nmp : NMP_Roots L V0 VL P (NNH_InstalledImpl.install (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2))
 (g1a : NNC_G1a (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) L V0 VL
   (NNH_InstalledImpl.install (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2))
 (R : RecSig (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r))
 (rs : RecSelect (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) R)
 (hb : HeadlineB (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) R)
 (nmfB : NNC_NMFPrimeB (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) L LIB_Deployed.deployed V0 VL P C
   (NNH_InstalledImpl.install (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2) g1a R)
 (r0 : NNC_R0Rep (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) V0)
 (a1 : NND_A1 (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) VL P C)
 (a2 : NND_A2 (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) L LIB_Deployed.deployed V0)
 (X : ExecB (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) R)
 (fx : X.Fixed) (w : X.World) (H : X.Oracle)
 (queries : X.QueriesF fx)
 (run : Runs (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r)
   (NNH_InstalledImpl.install (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2) (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H)) :
 (NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r).Bound (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H)
   ((NNH_HostEnv.install Sbase runtime).model1 (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H)) ((NNH_HostEnv.install Sbase runtime).model2 (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H)) ∧
 sp.Rest (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H) ((NNH_HostEnv.install Sbase runtime).model1 (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H)) ((NNH_HostEnv.install Sbase runtime).model2 (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H)) ∧
 (hb.OutcomeRec (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H) ((NNH_HostEnv.install Sbase runtime).model1 (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H)) ((NNH_HostEnv.install Sbase runtime).model2 (ctxB (S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r) X fx w H)) ∨
   X.ERec fx H) := by
 let S := NNE_RecordSig.physical (NNH_HostEnv.install Sbase runtime) d r
 let I := NNH_InstalledImpl.install (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2
 have nmn : NMN_Root L V0 VL I := ⟨NNH_064Install.refines⟩
 exact top_splitB_physical L LIB_Deployed.deployed V0 VL P C I sp hl a0 (NNH_LeafInstall.tx2 (NNH_064Install.install I0) allocation217 alloc1 alloc2 registry) nmx nms (NNH_LibraryStages.stages (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2)
   (NNH_InstalledImpl.dispatch L LIB_Deployed.deployed V0 VL P C (NNH_LeafInstall.install (NNH_064Install.install I0) allocation217) alloc1 alloc2) nmt nmp (NNH_LeafInstall.finish (NNH_064Install.install I0) allocation217 alloc1 alloc2) nmn
   g1a rs hb nmfB r0 a1 a2
   (NNE_RecordSig.a3 (NNH_HostEnv.install Sbase runtime) d r VL P C) (NNE_RecordSig.a4 (NNH_HostEnv.install Sbase runtime) d r L LIB_Deployed.deployed V0)
   (NNE_RecordSig.a5 (NNH_HostEnv.install Sbase runtime) d r L V0 VL P C I)
   (fun c => NNE_EntryArgs.count (d.e1 c) 3 (d.program c) (d.data1 c))
   (fun c => NNE_EntryArgs.count (d.e2 c) 7 (d.program c) (d.data2 c))
   X fx w H queries run

#print axioms deployed_splitB_conditional
end AspisR1.NNH_G0With064
