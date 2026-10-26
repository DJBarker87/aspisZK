import FinT_Model
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_AcceptedValue
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] QueryAccumulator.run QueryAccumulator.run22
  QueryResidualBridge.values QueryResidualBridge.basis
  OraclePortCheckpointStateC3.write OraclePortCheckpointStateC3.advance
variable {W : Type}

/-- Accepted source control uses physical equality only in the forward
 direction. No reverse-decoder/canonicality premise is needed. -/
theorem value (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a saved : verifier.Accumulator) (dot : E)
    (s2 : p.variant = .S2)
    (hd : ops.dot v.final_message a.weights.deref = ok (.Ok dot))
    (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (hi : input parsed q tr = some i) (hq : queries tr = some q)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing : Port4D_Pairing.PairingLaws (Port3_FinishStage.release ops)
      CheckpointBytes5Output.ofE v p i.data)
    (matched : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows parsed q tr) i.data)
    (dotMeaning : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, i.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
    (saved_ten : CheckpointBytes5Output.accumulator saved =
      (OraclePortCheckpointStateC3.write (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (twelve : CheckpointBytes5Output.accumulator a =
      OraclePortCheckpointStateC3.advance (model i.data (SelectedChallengeMap.rhoOf i.rho) q)
        12 (CheckpointBytes5Output.accumulator saved))
    (success : Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) :
    decide (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none =
      ok (.Ok ())) = OraclePortFrozen2.finish parsed q tr i (CheckpointBytes5Output.accumulator a) ∧
    decide (Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) =
      D0TypedChecks.verify (typedRows parsed q tr) i := by
  have returned := FinT_Returned.returned_state i q saved a saved_ten twelve
  have dotLaw : ∀ actual, ops.dot v.final_message a.weights.deref = ok (.Ok actual) →
      CheckpointBytes5Output.ofE actual = ∑ l : Fin 64, i.data.f l *
        LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l) := by
    intro actual ha
    have eq : actual = dot := core.result.Result.Ok.inj (Result.ok.inj (ha.symm.trans hd))
    exact eq ▸ dotMeaning
  have accepted := (Port4D_FinishFrozen.accepted_finish ops v p a parsed q tr i s2 read decoded
    pairing matched semantic dotLaw returned success).2.2
  have checks : D0TypedChecks.verify (typedRows parsed q tr) i = true := by
    have eq := OraclePortFrozen2.finish_value parsed q tr i hi hq
    rw [returned] at accepted
    rw [eq] at accepted
    exact accepted
  have native : Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none =
      ok (.Ok ()) := (Port3_QueryInstall.success_iff _ _).mp success
  exact ⟨(decide_eq_true native).trans accepted.symm,
    (decide_eq_true success).trans checks.symm⟩

#print axioms value
end AspisR1.SAF_AcceptedValue
end
