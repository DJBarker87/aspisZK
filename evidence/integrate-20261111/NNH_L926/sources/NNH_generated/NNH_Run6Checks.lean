import NNH_Run6Host
import NNH_Run6Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6Checks
open RSL TAS NNH_Libraries NNH_Run6Installed
variable (a217 : Bytes → Env → Bool) (a234 : TX2_234.Args → Env → Nat → Bool)
 (ch : NMX_R4_Authentication.Choices) (a1 a2 : NMV_ConcreteWindows.Allocation)
abbrev I := implementation a217 a234 ch a1 a2
example : (I a217 a234 ch a1 a2).f136 = NNG_Producer136.producer := rfl
example : (I a217 a234 ch a1 a2).f137 = NNG_Producer137.producer := rfl
example : (I a217 a234 ch a1 a2).f087 = NNG_Producer087.producer := rfl
example : (I a217 a234 ch a1 a2).f094 = NNG_ProducerFull094.producer := rfl
example : (I a217 a234 ch a1 a2).f328 = NNG_Producer328.producer := rfl
example : (I a217 a234 ch a1 a2).f345 = NNG_TotalProducer345.producer := rfl
example : (I a217 a234 ch a1 a2).f217 = NMX_R3_DecoderFold.decode a217 := rfl
example : (I a217 a234 ch a1 a2).f234 = NMX_R3_RegistryRoot.authenticate a234 := rfl
example : (I a217 a234 ch a1 a2).f233 = NMX_R4_Authentication.authenticate ch := rfl
example : (I a217 a234 ch a1 a2).f242 = NMX_R6_Validation.validate ch := rfl
example : (I a217 a234 ch a1 a2).f241 = NMX_R9_StageTwo.stage2 ch := rfl
example : (I a217 a234 ch a1 a2).f064 = NNH_064Install.f064 := rfl
example : (I a217 a234 ch a1 a2).f344 = NMV_ConcreteWindows.stage1 a1 NNG_TotalProducer345.producer := rfl
example : (I a217 a234 ch a1 a2).f240 = FIN_240.producer ch a2 := rfl
example : (I a217 a234 ch a1 a2).process = NVR_Dispatch.process
 (I a217 a234 ch a1 a2).f344 (I a217 a234 ch a1 a2).f240 := rfl
example : (I a217 a234 ch a1 a2).entry = NVR_Dispatch.entry (I a217 a234 ch a1 a2).process := rfl
example : LIB_Instances.D = LIBB_PoolLib.deployed := rfl
example : LIBB_PoolLib.deployed = LIB_Deployed.deployed := rfl
example : NNT_Field.Required ch =
 (∀ R0 w, RSL.NNT.LawRefines V0 R0 w → TX2_242.RowSpec_242 L D (I a217 a234 ch a1 a2).f242 →
 TX2_241.RowSpec_241 L D (lib V0 R0 w) (I a217 a234 ch a1 a2).f241) := rfl

/-- Ledger30's literal FIN slots, at its recorded fixed TX1 allocation stream.
No equality to FIN_330 is claimed for an arbitrary TX1 allocation stream. -/
theorem fin_slots :
 (I a217 a234 ch NNG_Candidate344.allocation a2).f344 = NNG_Candidate344.producer ∧
 (I a217 a234 ch NNG_Candidate344.allocation a2).f240 = FIN_240.producer ch a2 ∧
 (I a217 a234 ch NNG_Candidate344.allocation a2).process = FIN_333.producer ch a2 ∧
 (I a217 a234 ch NNG_Candidate344.allocation a2).entry = FIN_330.producer ch a2 :=
 ⟨rfl,rfl,rfl,rfl⟩

/-- Each delivery is checked at the closed literal implementation. -/
example : NMM_Roots L D V0 VL (I a217 a234 ch a1 a2) :=
 NNH_Run6Fields.nmm (I a217 a234 ch a1 a2) a217 a234 ch a1 a2
example : NMX_Root L D V0 VL (I a217 a234 ch a1 a2) :=
 NNH_Run6Fields.nmx (I a217 a234 ch a1 a2) a217 a234 ch a1 a2
example : RSL.NNT.NMS_RootsL L D V0 VL (I a217 a234 ch a1 a2) :=
 NNH_Run6Fields.nms (I a217 a234 ch a1 a2) a217 a234 ch a1 a2
example : NMV_Roots L D V0 VL P C (I a217 a234 ch a1 a2) :=
 NNH_Run6Fields.nmv (I a217 a234 ch a1 a2) a217 a234 ch a1 a2
example : NMW_Roots L D V0 VL P C (I a217 a234 ch a1 a2) :=
 NNH_Run6Fields.nmw (I a217 a234 ch a1 a2) a217 a234 ch a1 a2
example : NMT_Roots L V0 VL P C (I a217 a234 ch a1 a2) :=
 NNH_Run6Fields.nmt (I a217 a234 ch a1 a2) a217 a234 ch a1 a2
example : NMP_Roots L V0 VL P (I a217 a234 ch a1 a2) :=
 NNH_Run6Fields.nmp (I a217 a234 ch a1 a2) a217 a234 ch a1 a2
example : NMO_Root L V0 VL (I a217 a234 ch a1 a2) :=
 NNH_Run6Fields.nmo (I a217 a234 ch a1 a2) a217 a234 ch a1 a2
#print axioms fin_slots
end AspisR1.NNH_Run6Checks
end
