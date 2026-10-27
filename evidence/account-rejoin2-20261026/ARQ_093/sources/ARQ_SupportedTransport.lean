import ARQ_WorldSupport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_SupportedTransport
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

/-- Conditional all-world consumer. Supported is an UNPROVED implementation
obligation, not an adopted trust item or a new top premise. A fixed Rc9 game
at its supplied H does not establish this quantified support. -/
theorem clean {W A C Tx : Type} (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A)
    (c : DrvC_Installation.Configuration FIo_Install.W C) (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (root : Array U8 32#usize) (length : U32)
    (prior : Program Bytes State Unit) (words : CanonicalCutEnrichedTranscript.Words)
    (D : LiteralByteProtocol.Decoder)
    (owners : FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q0 Q1 : Nat) (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (support : ARQ_WorldSupport.Supported (Tx := Tx) L copy allocator c err r native1 native2 hashv a) :
    SCF_RequiredTransport.CleanAccountTransport (FIp_Install.configuration err c r) D hashv copy allocator CPH_Program.verifier
      a Q0 Q1 ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier) := by
  intro H
  dsimp only
  intro accepted clean
  obtain ⟨n⟩ := support H accepted
  have branch := ARQ_Join.accepted_recovery_or_account_collision L sdk copy std allocator a n.w1 n.w2 c err r
    native1 native2 hashv extraction n.sha256 H n.p1 n.syscall n.final1 n.final2 n.saved n.post1 n.post2
    n.admission1 n.admission2 n.accepted1 n.accepted2 root length prior words n.p n.t n.u n.actions
    n.game n.RuntimePersistence D owners Q0 Q1 prefixBound choiceBound accepted
  rcases branch with good | bad
  · have physical : ARQ_AccountView.physical (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H =
        F3T_Experiment.view
          ((eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).1,
           (F3T_Canon.canonInput (F3T_ByteCarrier.input (FIp_Install.configuration err c r)
             (submitted (eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2.1)),
            SCE_Experiment.accepted (eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2)) := by
      rw [first_projection]
      rfl
    rw [physical] at good
    exact good.2
  · exact False.elim (clean bad)

#print axioms clean
end AspisR1.ARQ_SupportedTransport
end
