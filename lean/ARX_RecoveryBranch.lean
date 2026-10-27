import ARQ_RecoveryCanonical
import ARQ_ObservedRecovery
import ARQ_PhysicalSampler
import ARQ_Canonical
import ARQ_AccountPreparation
import ARQ_SavedQueries
import ARX_CachedCharge
import SCG_AcceptedPair
import FIp_Canonical
import FIp_GlobalOwners
import F3Y_Canonical
import F3X_Charge
import F3X_AccountReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_RecoveryBranch
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- Direct account-recorder proof of the canonical branch, retaining source
acceptance as a local input to be supplied by ARQ_SourceAlternative. There is
no event-transport assumption and no source-recorder collision in the result. -/
theorem accepted {A F C : Type} (base : Configuration F C)
    (seed : AspisR1Stage2.Stage2Finish.FinishOps F)
    (installed : base.finish=FIn_Install.finishOps seed)
    (positions : base.stageBase.op22=ok 7527#usize ∧ base.stageBase.op21=ok 8007#usize ∧ base.stageBase.op20=ok 10055#usize)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (copy : S2Trust.Heap (Nat → S2W_D189Entry.Record) → Nat → S2Trust.Payload →
      S2W_TrustedStd.Outcome (Nat → S2W_D189Entry.Record))
    (allocator : S2W_D189Wrappers.Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (Q : Nat) (H : Bytes → State)
    (bound : ART_AdversaryWork.work (F3V_Install.configuration base) hashv copy allocator id a H ≤ Q) :
    let c := F3V_Install.configuration base
    ∀ (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonicalOwner : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domainOwner : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned)
    (finishOwners : FIp_GlobalOwners.Owners c base.boundaries),
    ∀ (aligned : sdk c = GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish
      c.reserved c.query c.geometry c.boundaries c.std)
    ,
    eval H (ART_PartialAccount.account c hashv copy allocator id a) =
      eval H (SCE_Experiment.account c hashv copy allocator id a) →
    SCE_Experiment.accepted (eval H (SCE_Experiment.account c hashv copy allocator id a)).2 = true →
    (eval H (F3T_Installed.source c hashv (input c (eval H (SCE_Experiment.submission a)).2))).2=true →
      eval H (F3T_Installed.source c hashv (input c (eval H (SCE_Experiment.submission a)).2)) =
        eval H (F3_Model.verifier D (input c (eval H (SCE_Experiment.submission a)).2)) ∧
      OraclePortRefineJoin.RecoveredInputAgreement (ARQ_AccountView.physical c hashv copy allocator id a H)
        (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program (ART_PartialAccount.account c hashv copy allocator id a)
          ARQ_Observer.project (ARQ_Observer.select c id))) := by
  dsimp only
  let c := F3V_Install.configuration base
  intro prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners aligned same accepted sourceSuccess
  obtain ⟨saved,post,final,post2,final2,reply,reply2⟩ :=
    SCG_AcceptedPair.replies c hashv copy allocator id a H accepted
  let s := SCE_Experiment.submitted (eval H a.first).2
  have success : (eval H (F3T_Installed.source c hashv (input c s))).2=true := by
    simpa only [SCE_Experiment.submission_eval] using sourceSuccess
  let account := ART_PartialAccount.account c hashv copy allocator id a
  obtain ⟨e,first,i,p,q,data,t,physical,stored,parser,query,found,calls,aux,shape,atPrepared,result⟩ :=
    ARQ_RecoveryCanonical.accepted base seed installed positions hashv s H w (F3X_Account.prior account)
      prepareOwner D primitiveOwner canonicalOwner domainOwner multiply one inverse success
  have inclusion := ARQ_AccountPreparation.included c aligned base.boundaries hashv copy allocator id
    a saved post final H reply e first
  have parsed : OraclePortCompactDraft.parse s.stored=some p := by
    have hp := (OraclePortStoredParserC4.parsed _ _ _ parser).1
    rw [stored,e.proofBytes] at hp
    exact hp
  have port := atPrepared.2.2.2.2.2.1
  obtain ⟨out,v,output,opening,prepared,log,guard⟩ := atPrepared.2.2.2.2.2.2
  have savedQueries := ARQ_SavedQueries.decoded c base.boundaries s H e prepareOwner primitiveOwner
    out output data.data q (SelectedChallengeMap.rhoOf data.rho) port
  have actualQueries : OraclePortCheckpointPreparedC5.decodeQueries
      (OraclePortCompactDraft.slice (bytesOf saved.val) 320 88)=some q := by
    rw [inclusion.1]
    exact savedQueries
  have project := ARQ_QueryProjection.on_reply c hashv copy allocator id a H saved post final p q reply parsed actualQueries
  have charge : AuS1_Finish.Collision H
      (F3V_Checkpoint.trace c base.boundaries s H e (F3X_Account.prior account)) p q →
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program account ARQ_Observer.project (ARQ_Observer.select c id))) := by
    intro collision
    apply ARX_CachedCharge.cached_preparation c hashv copy allocator id a Q H bound
      (F3X_Account.prior (F3X_Preparation.program c s)) p q (by rw [same]; exact project)
    · intro addr read
      rw [same]
      rw [F3X_Account.prior_log] at read
      exact inclusion.2 addr read
    · rw [F3X_Account.prior_log]
      have preparation := congrArg Prod.fst (F3X_Preparation.on_evidence c base.boundaries s H e)
      dsimp only at preparation
      unfold F3V_Checkpoint.trace at collision
      rw [F3X_Account.prior_log,←preparation] at collision
      exact collision
  have branch : eval H (F3T_Installed.source c hashv (input c s)) =
      eval H (F3_Model.verifier D (input c s)) ∧
      OraclePortRefineJoin.RecoveredInputAgreement (ARQ_AccountView.physical c hashv copy allocator id a H)
        (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program account ARQ_Observer.project (ARQ_Observer.select c id))) := by
    rcases result with collision | ⟨x,continuation⟩
    · exact Or.inr (charge collision)
    · rcases continuation (finishOwners s H e i p q data t atPrepared calls shape x) with collision | same
      · exact Or.inr (charge collision)
      · have rawFinal : eval H (F3T_Installed.source c hashv (input c (eval H (SCE_Experiment.submission a)).2)) =
            eval H (F3_Model.verifier D (input c (eval H (SCE_Experiment.submission a)).2)) := by
          simpa only [SCE_Experiment.submission_eval] using same.1
        have modelAccepted := ARQ_ModelAccepted.original c D hashv (SCE_Experiment.submission a) H sourceSuccess rawFinal
        have prepEval := congrArg Prod.fst (F3X_Preparation.on_evidence c base.boundaries s H e)
        dsimp only at prepEval
        have prepSampler := prepEval.trans (log.trans same.2)
        have common := ARQ_PhysicalSampler.chronological c aligned base.boundaries hashv copy allocator id a
          saved post final H reply e first prepSampler
        have agreement := ARQ_ObservedRecovery.agreement c D hashv copy allocator id a H modelAccepted common
        exact Or.inl ⟨same.1,agreement⟩
  simpa only [SCE_Experiment.submission_eval] using branch

#print axioms accepted
end AspisR1.ARX_RecoveryBranch
end
