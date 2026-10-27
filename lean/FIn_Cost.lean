import FIn_CollisionLaw
import FIn_Join
import F3Y_CollisionLaw
import F3U_SourceCost
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Cost
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open DrvC_Installation F3T_ByteCarrier F3T_TwoPass F3T_Experiment
open RawExtractorCostComposedV2 (Coins)
attribute [local irreducible] CostedAllocationLedgerM10.fixed GSActualBankJobsM10.count
  GSBankOutputEnvelopeM10.candidates InitialPublicImageWorkM10.budget

theorem source_cost {F C : Type} (base : Configuration F C)
    (seed : AspisR1Stage2.Stage2Finish.FinishOps F)
    (installed : base.finish=FIn_Install.finishOps seed)
    (positions : base.stageBase.op22=ok 7527#usize ∧ base.stageBase.op21=ok 8007#usize ∧ base.stageBase.op20=ok 10055#usize)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : ByteProver) (Q : Nat) (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    let c := F3V_Install.configuration base
    ∀ (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonicalOwner : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domainOwner : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned)
    (finishOwners : FIn_GlobalOwners.Owners c base.boundaries),
    ∀ (H : Bytes → State),
    (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P)))).2.2=true →
    mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
      (view (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P))))) coins).2.total : Rat))≤
      ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P) F3X_Projection.project select)) := by
  dsimp only
  let c := F3V_Install.configuration base
  intro prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners H accepted
  have priorQueries : ∀ H : Bytes → State,(eval H (F3X_Account.prior P)).1.length≤Q := by
    intro H
    rw [F3X_Account.prior_log]
    exact queries H
  have join := FIn_CollisionLaw.joined base seed installed positions hashv D w (F3X_Account.prior P) Q priorQueries select
    prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners
  rcases F3U_SourceCost.cost_or_collision c D P Q queries hashv _ join H accepted with cost | hit
  · exact Or.inl cost
  · exact Or.inr ((F3Y_Event.actual c hashv P Q select H).mp hit)

#print axioms source_cost
end AspisR1.FIn_Cost
end
