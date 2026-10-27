import BEn_Statements
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_Final
open Aeneas Aeneas.Std Result SdkC_Source
open S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open F3T_ByteCarrier F3T_Experiment

/-- Projecting the same reached Prepared operands commutes definitionally with
the sole D188_TRACE_BOUNDARY recorder. The array form does not introduce a
second native attribution or independent native observation. -/
theorem same_native {S : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest) (input : BEn_ExtractedTrace.Input) (slot : Fin 2)
    (state : S) (before : Log) :
    BEn_ExtractedSlots.native call hashv
      ⟨input.proof,input.prepared.queries,input.prepared.roots,input.folded⟩ slot state before =
      BEn_ExtractedTrace.native call hashv input slot state before := rfl

/-- Lean checks the two complete dependent theorem types agree. Their proofs
also agree: no output strengthening or local-law premise is hidden here. -/
theorem unchanged_root : @BEn_Top.deployed = @ARX_Root.deployed := rfl

/-- The SAME admitted account supplies the local native/source laws AND the
existing global event/recorder alternative. No successful account is swapped
for another existential witness, and no global P1 at H is added. -/
theorem joint {W A C Tx : Type} (L : Library W (Nat → Record))
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
    (let cfg := FIp_Install.configuration err c r
    ∃ f s, SourceCuts (DrvC_Installation.sdk cfg) (eval H a.first).2.entry.first
      ((eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.second secondSizes)
      n.entry.saved f s ∧
      n.entry.post2 = (eval H (a.second (eval H a.first).2 n.entry.saved n.entry.post1 n.entry.final1)).2.entry.heap ∧
      ∃ (p0 : AspisR1CurrentCaller.verifier.Prepared) (root0 : Digest)
        (p1 : VTop_Stages.verifier.Prepared) (root1 : Digest),
        Op5T_Install.currentBatch Port4B_Install.leaves (DrvC_Installation.currentDigest cfg)
          f.proof p0 root0 0#usize () = ok (.Ok ()) ∧
        Op5T_Install.stageBatch Port4B_Install.leaves (DrvC_Installation.digest cfg)
          s.proof p1 root1 1#usize () = ok (.Ok ()) ∧
        ∀ (S : Type) (call : Parts → S → Result Digest × S) (state : S) (before : Log),
          BEh_Scope.Law
            (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.currentBody hashv f.proof p0 root0) state before)
            (BEf_Carrier.run call (SdkC_BatchSource.currentCode hashv f.proof p0 root0) state before) ∧
          BEh_Scope.Law
            (BEn_ExtractedSlots.observe call (BEn_ExtractedSlots.stageBody hashv s.proof p1 root1) state before)
            (BEf_Carrier.run call (SdkC_BatchSource.stageCode hashv s.proof p1 root1) state before)) ∧
    ((eval H (F3T_Installed.source (FIp_Install.configuration err c r) hashv
      (input (FIp_Install.configuration err c r) (eval H (submission a)).2)) =
        eval H (F3_Model.verifier D (input (FIp_Install.configuration err c r) (eval H (submission a)).2)) ∧
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a))))).2.2 = true ∧
      OraclePortRefineJoin.RecoveredInputAgreement
        (ART_PhysicalView.physical (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H)
        (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a)))))) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program
        (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier)))) := by
  exact ⟨BEn_AdmittedCuts.selected L copy allocator c err r native1 native2 hashv extraction a H n std,
    BEn_AccountComposition.accepted L copy allocator c err r native1 native2 hashv extraction a H n
      std D words owners Q bound⟩

#print axioms joint

#print axioms same_native
#print axioms unchanged_root
#print axioms BEn_Top.deployed
#print axioms BEn_LocalAssociation.observation
#print axioms BEn_AdmittedCuts.selected
end AspisR1.BEn_Final
end
