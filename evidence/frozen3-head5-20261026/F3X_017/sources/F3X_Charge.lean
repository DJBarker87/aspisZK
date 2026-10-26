import F3X_AccountPrior
import F3X_CollisionErase
import F3V_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_Charge
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem prefix_collision {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission) (H : Bytes → State)
    (e : Evidence c B s H) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (prior : Program Bytes State Unit) (Q : Nat)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (budget : ∀ H : Bytes → State,FS.firstReads FS.emptyTable
      (eval H (F3X_AccountPrior.program c hashv prior s)).1≤Q+1921)
    (success : (eval H (F3T_Installed.source c hashv (input c s))).2=true)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (parser : OraclePortCompactDraft.parse s.stored=some p)
    (port : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared e.run.p) data q rho)
    (collision : AuS1_Finish.Collision H
      (F3V_Checkpoint.trace c B s H e
        (F3X_Account.prior (F3X_AccountPrior.program c hashv prior s))) p q) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior s)
        F3X_Projection.project select)) := by
  let account := F3X_AccountPrior.program c hashv prior s
  have accountEval := F3X_AccountPrior.evaluation c hashv prior s H
  rw [F3X_Account.accepted c B s H e hashv success] at accountEval
  have project : F3X_Projection.project (eval H account).2=(p,q) := by
    change F3X_Projection.project (eval H (F3X_AccountPrior.program c hashv prior s)).2=_
    rw [accountEval]
    exact F3X_Projection.on_prepared s e.run.p p q data rho parser port
  let prep := (eval H (F3X_Preparation.program c s)).1
  have included : ∀ a,FS2.Duplex.Read prep a → FS2.Duplex.Read (eval H account).1 a := by
    intro a read
    change a∈(eval H (F3X_AccountPrior.program c hashv prior s)).1.map Prod.fst
    rw [accountEval,List.map_append,List.map_append]
    exact List.mem_append_right _ (List.mem_append_right _ read)
  have erase := F3X_CollisionErase.same H (eval H account).1 prep p q
    (Op5I_AcceptedCarrierCounterexample.evaluated_reply H account)
    (Op5I_AcceptedCarrierCounterexample.evaluated_reply H (F3X_Preparation.program c s)) included
  have hit : AuS1_Finish.Collision H ((eval H account).1++prep) p q := by
    have prepEval := congrArg Prod.fst (F3X_Preparation.on_evidence c B s H e)
    unfold F3V_Checkpoint.trace at collision
    rw [F3X_Account.prior_log] at collision
    rw [←prepEval] at collision
    exact collision
  have sourceHit := erase.mp hit
  apply F3U_AccountEvent.charged account F3X_Projection.project select Q budget H
  rw [project]
  exact sourceHit

#print axioms prefix_collision
end AspisR1.F3X_Charge
end
