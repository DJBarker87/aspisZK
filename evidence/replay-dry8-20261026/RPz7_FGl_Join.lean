import RPz7_FGl_Canonical
import RPz7_F3X_Charge
import RPz7_F3X_AccountReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_Join
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

/-- Acceptance-guarded L157 replacement on every byte submission and every H.
The right disjunct is literally the SINGLE charged complete-account event,
including its recorded source, canonical replay and history audit. -/
theorem accepted_raw_join_or_collision {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (prior : Program Bytes State Unit) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H prior).1.length≤Q)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    let c := F3V_Install.configuration base
    ∀ (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonicalOwner : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domainOwner : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned)
    (finishOwners : FGl_PreparedAt.Owners c base.boundaries),
    ∀ (s : Submission) (H : Bytes → State),
    (eval H (F3T_Installed.source c hashv (input c s))).2=true →
      eval H (F3T_Installed.source c hashv (input c s))=
        eval H (F3_Model.verifier D (input c s)) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior s)
          F3X_Projection.project select)) := by
  dsimp only
  let c := F3V_Install.configuration base
  intro prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners s H success
  let account := F3X_AccountPrior.program c hashv prior s
  obtain ⟨e,i,p,q,data,t,physical,stored,parser,query,found,calls,atPrepared,result⟩ :=
    FGl_Canonical.accepted base hashv s H w (F3X_Account.prior account)
      prepareOwner D primitiveOwner canonicalOwner domainOwner multiply one inverse success
  have parsed : OraclePortCompactDraft.parse s.stored=some p := by
    have firstParser := (OraclePortStoredParserC4.parsed _ _ _ parser).1
    rw [stored,e.proofBytes] at firstParser
    exact firstParser
  have port := atPrepared.2.2.2.2.2.1
  have charge : AuS1_Finish.Collision H
      (F3V_Checkpoint.trace c base.boundaries s H e (F3X_Account.prior account)) p q →
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program account F3X_Projection.project select)) := by
    intro collision
    exact F3X_Charge.prefix_collision c base.boundaries s H e hashv prior Q select
      (F3X_AccountReads.bound base hashv prior s Q queries D w) success p q data.data
      (SelectedChallengeMap.rhoOf data.rho) parsed port collision
  rcases result with collision | ⟨x,continuation⟩
  · exact Or.inr (charge collision)
  · rcases continuation (finishOwners s H e i p q data t atPrepared calls x) with collision | same
    · exact Or.inr (charge collision)
    · exact Or.inl same

#print axioms accepted_raw_join_or_collision
end AspisR1.FGl_Join
end
