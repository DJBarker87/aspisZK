import F3X_Join
import F3X_JointCongr
import F3U_ConditionalBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_Bound
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3T_Runtime

theorem bound {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : ByteProver) (Q : Nat) (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (runtime : Runtime)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    let c := F3V_Install.configuration base
    ∀ (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonicalOwner : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domainOwner : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned)
    (finishOwners : F3X_PreparedAt.Owners c base.boundaries)
    (L159_StoredCarrierBinding : StoredCarrierBinding c D (F3T_Installed.source c hashv) P runtime),
    F3T_RuntimeBound.failureModel runtime≤F3T_Numeric.total Q := by
  dsimp only
  let c := F3V_Install.configuration base
  intro prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners binding
  let prior := F3X_Account.prior P
  have priorQueries : ∀ H : Bytes → State,(eval H prior).1.length≤Q := by
    intro H
    rw [F3X_Account.prior_log]
    exact queries H
  let bad : F3U_CollisionJoin.Exception := fun H pub stored=>
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior ⟨pub,stored⟩)
        F3X_Projection.project select))
  have join : F3U_CollisionJoin.Join c D (F3T_Installed.source c hashv) bad :=
    F3X_Join.accepted_raw_join_or_collision base hashv D w prior Q priorQueries select
      prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners
  let account := F3X_Account.program c hashv P
  have accountBudget : ∀ H : Bytes → State,FS.firstReads FS.emptyTable (eval H account).1≤Q+1921 := by
    intro H
    rw [←F3X_AccountPrior.actual c hashv P H]
    exact F3X_AccountReads.bound base hashv prior (eval H P).2 Q priorQueries D w H
  apply F3U_ConditionalBound.bound c D P Q queries hashv runtime bad join binding
    account F3X_Projection.project select accountBudget
  intro H hit
  have same := F3X_JointCongr.evaluation _ account F3X_Projection.project select H
    (F3X_AccountPrior.actual c hashv P H)
  change BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
    (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior (eval H P).2)
      F3X_Projection.project select)) at hit
  rw [same] at hit
  exact hit

#print axioms bound
end AspisR1.F3X_Bound
end
