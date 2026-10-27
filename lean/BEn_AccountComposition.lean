import BEn_OriginalAssociation
import BEn_ReachedLaws
import ARX_Join
import ARU_Charges
import RPx_Transport
import RPx_AccountCharge
import BEl_AccountComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_AccountComposition
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open F3T_ByteCarrier F3T_Experiment

/-- Historical final global interface is literally ARQ_Join.Target.
The adopted ARX admitted game now supplies its own pointwise join below. -/
abbrev LegacyJoin := @ARQ_Join.Target

theorem accepted {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q : Nat) (bound : ART_AdversaryWork.work (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a H ≤ Q) :
    (eval H (F3T_Installed.source (FIp_Install.configuration err c r) hashv
      (input (FIp_Install.configuration err c r) (eval H (submission a)).2)) =
        eval H (F3_Model.verifier D (input (FIp_Install.configuration err c r) (eval H (submission a)).2)) ∧
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a))))).2.2 = true ∧
      OraclePortRefineJoin.RecoveredInputAgreement
        (ART_PhysicalView.physical (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H)
        (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a)))))) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program
        (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier))) := by
  exact ARX_Join.accepted L copy allocator c err r native1 native2 hashv extraction a H n
    std D words owners Q bound

#print axioms accepted
#print axioms BEl_AccountComposition.conditional
#print axioms RPx_Transport.transport
#print axioms RPx_AccountCharge.charged
#print axioms ARU_Charges.charged
end AspisR1.BEn_AccountComposition
end
