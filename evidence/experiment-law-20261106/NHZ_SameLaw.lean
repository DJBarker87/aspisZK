import NHZ_NativeAssociation
import NGS_PersistedCarriers
import RPz8_ARW_AdmittedSupport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHZ_EXPERIMENT
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound SCE_Experiment
attribute [local instance] Classical.propDecidable

section
variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
local notation "cfg" => FIp_Install.configuration err c r
local notation "source" => ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
/-- Turn the two actual chronological observations into source-log agreement.
`entry` retains precisely the approved game, accepted pair and runtime admissions;
HISTORY/CARRIERS cannot manufacture these facts or the second native log. -/
theorem support_from_events (H : Bytes → State)
    (entry : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (firstObserved : NGP_L181.Observation _)
    (secondObserved : NGP_L181.Observation _)
    (firstNative : NGP_L181.NativeAssociation hashv (ARS_NativeAccount.firstSyntax cfg hashv copy allocator CPH_Program.verifier (eval H a.first).2) firstObserved)
    (secondNative : NGP_L181.NativeAssociation hashv (ARS_NativeAccount.secondSyntax cfg hashv allocator CPH_Program.verifier
      (eval H (a.second (eval H a.first).2 entry.saved entry.post1 entry.final1)).2) secondObserved)
    (firstAgrees : ARS_QueryTransport.Agrees H firstObserved.attempted)
    (secondAgrees : ARS_QueryTransport.Agrees H secondObserved.attempted) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  refine ⟨⟨entry,?_,?_⟩⟩
  · have log := congrArg Prod.snd firstNative
    change firstObserved.attempted = _ at log
    rw [← log]
    exact firstAgrees
  · have log := congrArg Prod.snd secondNative
    change secondObserved.attempted = _ at log
    rw [← log]
    exact secondAgrees

/-- Same response-selected adaptive execution, exact account replay, and
admitted support on its full cylinder. Consistency includes both reached phases,
verifier prefixes, and duplicate occurrences; no honest-run restriction. -/
theorem replay_support
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk cfg) native1 native2 hashv)
    (native H : Bytes → State)
    (entry : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (consistent : ARS_AccountReplay.Consistent source native H) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    eval H source = eval native source :=
  ARW_AdmittedSupport.original L copy allocator c err r native1 native2 hashv extraction a native H entry syscall consistent

/-- Uses the original L154 issued budget, SAME failureMass, recorder and single
Q+2965 event. This does not infer physical observation realization from slices. -/
theorem pointwise_from_events
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk cfg) native1 native2 hashv)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FIp_GlobalOwners.Owners cfg
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q0 Q1 : Nat)
    (queries : ∀ K, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a K).length ≤ Q0+Q1)
    (H : Bytes → State)
    (entry : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (firstObserved : NGP_L181.Observation _)
    (secondObserved : NGP_L181.Observation _)
    (firstNative : NGP_L181.NativeAssociation hashv (ARS_NativeAccount.firstSyntax cfg hashv copy allocator CPH_Program.verifier (eval H a.first).2) firstObserved)
    (secondNative : NGP_L181.NativeAssociation hashv (ARS_NativeAccount.secondSyntax cfg hashv allocator CPH_Program.verifier
      (eval H (a.second (eval H a.first).2 entry.saved entry.post1 entry.final1)).2) secondObserved)
    (firstAgrees : ARS_QueryTransport.Agrees H firstObserved.attempted)
    (secondAgrees : ARS_QueryTransport.Agrees H secondObserved.attempted) :
    RawRecordedOracleExtractionMassBin.failureMass (ART_PhysicalView.physical cfg hashv copy allocator CPH_Program.verifier a H) ≤
      RawRecordedOracleExtractionMassBin.failureMass (eval H
        (F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a))))) +
      indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program source ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)))) := by
  obtain ⟨support⟩ := support_from_events L copy allocator c err r native1 native2 hashv a H entry
    firstObserved secondObserved firstNative secondNative firstAgrees secondAgrees
  have budget := ARW_AdmittedBudget.issued L copy allocator c err r native1 native2 hashv extraction a H support Q0 Q1 queries
  exact ARX_Domination.pointwise L copy allocator c err r native1 native2 hashv extraction a H support std D words owners (Q0+Q1) budget.1

/-- Exact observable projection required to instantiate the existing admitted
runtime with a physical experiment. This is an OPEN producer obligation, not a
runtime trust row. It retains the entire occurrence log and RunView, including
stored/public/fail event; outside the approved game the result is none. -/
def Realizes (physical : F3T_Runtime.Runtime) : Prop :=
  ∀ H, eval H physical = eval H (ARX_AdmittedRuntime.runtime (Tx := Tx)
    L copy allocator c err r native1 native2 hashv a)

/-- Conditional transport under the original, unconditioned ROM weights.
No physical Realizes witness is constructed here. The planned physical
same_law remains OPEN until the producer supplies it on this SAME adversary. -/
theorem same_law
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk cfg) native1 native2 hashv)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FIp_GlobalOwners.Owners cfg
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q0 Q1 : Nat)
    (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
    (physical : F3T_Runtime.Runtime)
    (realizes : Realizes (Tx := Tx) L copy allocator c err r native1 native2 hashv a physical) :
    F3T_Runtime.deployedFailure physical =
      F3T_Runtime.deployedFailure (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) ∧
    F3T_Runtime.deployedFailure physical ≤
      lazyMean (F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift cfg (submission a)))) FS.emptyTable
        RawRecordedOracleExtractionMassBin.failureMass + F3T_Numeric.accountLoss (Q0+Q1) ∧
    F3T_RuntimeBound.failureModel physical ≤ F3T_Numeric.total (Q0+Q1) := by
  have massEq : F3T_Runtime.deployedFailure physical =
      F3T_Runtime.deployedFailure (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) :=
    OracleProgramLawExt.lazyMean_eq_of_eval _ _ _ _ (fun H => congrArg F3T_Runtime.runtimeMass (realizes H))
  refine ⟨massEq,?_,?_⟩
  · rw [massEq]
    exact ARX_Mass.bounded (Tx := Tx) L copy allocator c err r native1 native2 hashv a extraction std D words owners Q0 Q1 queries
  · have numeric := ARX_Residual.numeric (Tx := Tx) L copy allocator c err r native1 native2 hashv extraction a std D words owners Q0 Q1 queries
    unfold F3T_RuntimeBound.failureModel at *
    rw [massEq]
    exact numeric

#print axioms support_from_events
#print axioms replay_support
#print axioms pointwise_from_events
#print axioms same_law
end
end AspisR1.NHZ_EXPERIMENT
