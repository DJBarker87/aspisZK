import ARS_Coverage
import ARQ_Domination
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_CylinderDomination
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.CausalFirstHitUnionBound
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

/-- Compose the actual ARQ failure-mass consumer with query-restricted replay.
The RHS is explicitly at native, so this is not an unconditional ROM average. -/
theorem pointwise {W A C Tx : Type} (L : Library W (Nat → Record))
    (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (err : C)
    (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native H : Bytes → State)
    (n : ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (consistent : ARS_AccountReplay.Consistent
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H)
    (root : Array U8 32#usize) (length : U32)
    (prior : Program Bytes State Unit) (words : CanonicalCutEnrichedTranscript.Words)
    (D : LiteralByteProtocol.Decoder)
    (owners : FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q0 Q1 : Nat) (prefixBound : ∀ K, (eval K a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final K, (eval K (a.second i saved post final)).1.length ≤ Q1) :
    F3T_Runtime.runtimeMass (eval H (runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)) ≤
      RawRecordedOracleExtractionMassBin.failureMass
        (eval native (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a))))) +
      indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval native (Hiq_RecordedJoint.program
          (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
          ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier)))) := by
  rw [ARS_AccountReplay.runtime _ hashv copy allocator CPH_Program.verifier a native H consistent]
  exact ARQ_Domination.pointwise L sdk copy std allocator a n.w1 n.w2 c err r
    native1 native2 hashv extraction n.sha256 native n.p1 n.syscall n.final1 n.final2 n.saved n.post1 n.post2
    n.admission1 n.admission2 n.accepted1 n.accepted2 root length prior words n.p n.t n.u n.actions
    n.game n.RuntimePersistence D owners Q0 Q1 prefixBound choiceBound

#print axioms pointwise
end AspisR1.ARS_CylinderDomination
end
