import Port4D_FinishInstall
import Port4D_Pairing
import OraclePortFrozen2Checkpoint
import Port4D_FlushRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_FinishFrozen
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] QueryAccumulator.run22 QueryResidualBridge.values QueryResidualBridge.basis
variable {W : Type}

/-- Every query was checked in the same saved-ten/resumed-twelve chain.
This lemma supplies the typed decision without assuming its acceptance. -/
theorem query_decision (i : SourceInputs) (q : Fin 22 → Fin 262144)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (matched : ∀ j, MatchingSupport.match0 i.data (q j)) :
    R16DecisionQueryModel.verify i.data i.queryBytes = true := by
  have hpref : R15WriterModel.Prefix i.data q 10 := fun j _ => matched j
  simp only [R16DecisionQueryModel.verify,decoded]
  unfold R16DecisionCheckpoint.decision R16DecisionCheckpoint.tx1
  rw [if_pos hpref]
  change decide (10 = 10 ∧ ∀ j : Fin 22, 10 ≤ j.val → MatchingSupport.match0 i.data (q j)) = true
  exact decide_eq_true ⟨rfl,fun j _ => matched j⟩

/-- Accepted finish on the actual materialized returned state. Session A's
S3/S4/S5/S9 frontiers are named, never hidden inside a finish equality.
The exact returned-state advance is the separate query/flush row obligation. -/
theorem accepted_finish (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (s2 : p.variant = .S2)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release ops)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows parsed q tr) i.data)
    (dot_S5 : ∀ actual, ops.dot v.final_message a.weights.deref = ok (.Ok actual) →
      CheckpointBytes5Output.ofE actual = ∑ l : Fin 64, i.data.f l * LiteralOpeningView.eK
        ((CheckpointBytes5Output.accumulator a).weights l))
    (returned_S7_S8 : CheckpointBytes5Output.accumulator a =
      OraclePortFrozen2.completeState i q)
    (success : Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) :
    ops.dot v.final_message a.weights.deref =
      ok (.Ok a.rhs) ∧
    a.next = 22#usize ∧
    OraclePortFrozen2.finish parsed q tr i
      (CheckpointBytes5Output.accumulator a) = true := by
  have retained : Port3_FinishStage.finish ops v p a none = ok (.Ok ()) :=
    (Port4D_FinishInstall.retained_eq ops v p a none).symm.trans success
  obtain ⟨physical,next⟩ := Port4D_FinishInstall.accepted_dot ops v p a none success
  have control := (Port3_QueryInstall.success_iff _ _).mp retained
  rw [Port3_FinishStage.parent_eq] at control
  have compare : Port4D_Pairing.ComparisonLaw (Port3_FinishStage.release ops) CheckpointBytes5Output.ofE := by
    intro x y h
    exact congrArg CheckpointBytes5Output.ofE (Port3_FinishStage.ne_false x y h)
  have two : (Port3_FinishStage.release ops).folds p.variant = ok 2#usize := by rw [s2]; rfl
  have pairing := Port4D_Pairing.finish_pairingChecks (Port3_FinishStage.release ops)
    CheckpointBytes5Output.ofE compare v p a none _ i.data read pairing_S3_S5_S9 two control
  have dot := dot_S5 a.rhs physical
  have sum : (∑ l : Fin 64, i.data.f l * LiteralOpeningView.eK
      ((CheckpointBytes5Output.accumulator a).weights l)) = (CheckpointBytes5Output.accumulator a).rhs := dot.symm
  have closed : HchecksAccumulator.ClosedSum LiteralOpeningView.eK i.data q (SelectedChallengeMap.rhoOf i.rho) := by
    rw [returned_S7_S8] at sum
    simpa only [OraclePortFrozen2.completeState,QueryAccumulator.run22_weights,
      QueryAccumulator.run22_rhs,HchecksAccumulator.ClosedSum] using sum
  have checks : D0TypedChecks.verify (typedRows parsed q tr) i = true := by
    simp only [D0TypedChecks.verify,read,decide_eq_true_eq]
    refine ⟨True.intro,pairing,query_decision i q decoded matches_S4_S7,semantic_S3_S9,?_⟩
    intro q' hd
    have eq : q' = q := Option.some.inj (hd.symm.trans decoded)
    subst q'
    exact closed
  refine ⟨physical,next,?_⟩
  simp only [OraclePortFrozen2.finish,checks,Bool.true_and,decide_eq_true_eq]
  exact sum

#print axioms query_decision
#print axioms accepted_finish
end AspisR1.Port4D_FinishFrozen
end
