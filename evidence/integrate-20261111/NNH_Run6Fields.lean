import NNT_Field
import NNT_G1aLaw
import NNN_InstalledChecks
import NNH_Run5bHost
import NNH_Run5bAcceptance
import NNH_Run5bHeadlineB
import NNH_Run5bSplit
import NNH_Run5bFullSpace
import LIBB_PoolNoWrite
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6Fields
open RSL TAS NNH_Libraries

def children (I0 : Impl L V0 VL) (allocation217 : Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) : Impl L V0 VL :=
 { I0 with
   f136 := NNG_Producer136.producer
   f137 := NNG_Producer137.producer
   f087 := NNG_Producer087.producer
   f094 := NNG_ProducerFull094.producer
   f328 := NNG_Producer328.producer
   f345 := NNG_TotalProducer345.producer
   f217 := NMX_R3_DecoderFold.decode allocation217
   f234 := NMX_R3_RegistryRoot.authenticate allocation234
   f233 := NMX_R4_Authentication.authenticate ch
   f242 := NMX_R6_Validation.validate ch
   f241 := NMX_R9_StageTwo.stage2 ch
   f064 := NNH_064Install.f064 }

def install (I0 : Impl L V0 VL) (allocation217 : Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation) :=
 NVR_TAS.install (NVR_TasRoots.implementation (children I0 allocation217 allocation234 ch) alloc1 alloc2)

variable (I0 : Impl L V0 VL) (allocation217 : Bytes → Env → Bool) (allocation234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
abbrev I := install I0 allocation217 allocation234 ch alloc1 alloc2

def nmm : NMM_Roots L D V0 VL (I I0 allocation217 allocation234 ch alloc1 alloc2) :=
 ⟨NMX_R3_DecoderFold.root allocation217, NMX_R3_RegistryRoot.root allocation234⟩
def nmx : NMX_Root L D V0 VL (I I0 allocation217 allocation234 ch alloc1 alloc2) :=
 ⟨fun _ _ => NMX_R4_Authentication.root ch⟩
def nms : RSL.NNT.NMS_RootsL L D V0 VL (I I0 allocation217 allocation234 ch alloc1 alloc2) :=
 ⟨fun _ => NMX_R6_Validation.root ch, NNT_Field.r241 ch⟩
def nmv : NMV_Roots L D V0 VL P C (I I0 allocation217 allocation234 ch alloc1 alloc2) :=
 { r240 := NVR_TasRoots.field240 L D V0 VL (children I0 allocation217 allocation234 ch) alloc1 alloc2
   r344 := NVR_TasRoots.field344 L V0 VL P C (children I0 allocation217 allocation234 ch) alloc1 alloc2
   g2 := fun law hw a s env o h => NVR_G2Reference.frame L D V0 LIBB_PoolNoWrite.laws law hw a s env o h }
def nmw : NMW_Roots L D V0 VL P C (I I0 allocation217 allocation234 ch alloc1 alloc2) :=
 NVR_TAS.roots L D V0 VL P C (NVR_TasRoots.implementation (children I0 allocation217 allocation234 ch) alloc1 alloc2)
def nmt : NMT_Roots L V0 VL P C (I I0 allocation217 allocation234 ch alloc1 alloc2) :=
 ⟨fun _ => NNG_Candidate094.candidate, fun _ => NNG_Candidate328.candidate,
  fun _ => NNG_ActualCandidate345.candidate⟩
def nmp : NMP_Roots L V0 VL P (I I0 allocation217 allocation234 ch alloc1 alloc2) :=
 ⟨fun _ => NNG_Candidate137.candidate, fun _ => NNG_Candidate087.candidate⟩
def nmo : NMO_Root L V0 VL (I I0 allocation217 allocation234 ch alloc1 alloc2) :=
 ⟨NNG_Candidate136.candidate⟩
example : LIB_Instances.D = LIBB_PoolLib.deployed := rfl
example : LIBB_PoolLib.deployed = LIB_Deployed.deployed := rfl
example : (I I0 allocation217 allocation234 ch alloc1 alloc2).f241 = NMX_R9_StageTwo.stage2 ch := rfl
example : (I I0 allocation217 allocation234 ch alloc1 alloc2).f064 = NNH_064Install.f064 := rfl
#print axioms children
#print axioms install
#print axioms nmm
#print axioms nmx
#print axioms nms
#print axioms nmv
#print axioms nmw
#print axioms nmt
#print axioms nmp
#print axioms nmo
end AspisR1.NNH_Run6Fields
end
