import FinT_Pairing
import FinT_Returned
import Port4D_ReturnedFinish
import RowFinish_Finalization

set_option autoImplicit false
noncomputable section
namespace AspisR1.FinT_Model
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
attribute [local irreducible] QueryAccumulator.run QueryAccumulator.run22
  QueryResidualBridge.values QueryResidualBridge.basis
  OraclePortCheckpointStateC3.write OraclePortCheckpointStateC3.advance
variable {W : Type}

/-- Whole source acceptance value, including rejection, on the returned
state. S3/S4/S5/S9 total primitive evaluations and canonicality are explicit
owner hypotheses. Neither source finish success nor model acceptance is a
premise. Pure local leaves do not claim a native runtime/ROM instance. -/
theorem finish_value (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a saved : verifier.Accumulator) (alpha0 alpha1 : E)
    (r0 : RoundValues ops v.round0 alpha0 p.claim)
    (r1 : RoundValues ops v.round1 alpha1 r0.value)
    (weights : W) (alphas : Slice E) (pair dot : E)
    (s2 : p.variant = .S2)
    (ha0 : Array.index_usize p.alpha 0#usize = ok alpha0)
    (ha1 : Array.index_usize p.alpha 1#usize = ok alpha1)
    (hw : ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (has : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas)
    (hp : ops.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (hd : ops.dot v.final_message a.weights.deref = ok (.Ok dot))
    (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (hi : input parsed q tr = some i) (hq : queries tr = some q)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release ops)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows parsed q tr) i.data)
    (dot_S5 : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, i.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
    (canonical_S3_S4_S5_S9 : ∀ x ∈ [r0.lhs,r0.rhs,r1.lhs,r1.rhs,pair,r1.value,dot,a.rhs],
      CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE x) = x)
    (saved_ten : CheckpointBytes5Output.accumulator saved =
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (twelve : CheckpointBytes5Output.accumulator a =
      OraclePortCheckpointStateC3.advance (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q) 12 (CheckpointBytes5Output.accumulator saved)) :
    decide (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none =
      ok (.Ok ())) = OraclePortFrozen2.finish parsed q tr i (CheckpointBytes5Output.accumulator a) ∧
    decide (Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) =
      D0TypedChecks.verify (typedRows parsed q tr) i := by
  let decode := CheckpointBytes5Output.ofE
  have returned := FinT_Returned.returned_state i q saved a saved_ten twelve
  have nextVal : a.next.val = 22 := by
    have h := congrArg QueryAccumulator.State.next returned
    simpa only [CheckpointBytes5Output.accumulator,OraclePortFrozen2.completeState,
      QueryAccumulator.run22_next] using h
  have next : a.next = 22#usize := UScalar.eq_of_val_eq nextVal
  have strict (x y : E) (hx : x ∈ [r0.lhs,r0.rhs,r1.lhs,r1.rhs,pair,r1.value,dot,a.rhs])
      (hy : y ∈ [r0.lhs,r0.rhs,r1.lhs,r1.rhs,pair,r1.value,dot,a.rhs]) :
      x = y ↔ decode x = decode y := by
    exact FinT_Comparisons.canonical_eq x y (canonical_S3_S4_S5_S9 x hx)
      (canonical_S3_S4_S5_S9 y hy)
  have gates : (r0.lhs = r0.rhs ∧ r1.lhs = r1.rhs ∧ pair = r1.value) ↔
      LiteralPairingChecks.checks (typedRows parsed q tr) := by
    have pg := FinT_Pairing.gates CheckpointBytes5Output.ofE CheckpointBytes4ReaderFields.sourceE
      ops v p alpha0 alpha1 r0 r1 weights alphas pair s2 ha0 ha1 hw has hp i.data pairing_S3_S5_S9
      (canonical_S3_S4_S5_S9 r0.lhs (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]))
      (canonical_S3_S4_S5_S9 r0.rhs (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]))
      (canonical_S3_S4_S5_S9 r1.lhs (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]))
      (canonical_S3_S4_S5_S9 r1.rhs (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]))
      (canonical_S3_S4_S5_S9 pair (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]))
      (canonical_S3_S4_S5_S9 r1.value (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]))
    exact pg.trans (LiteralPairingChecks.acceptedPairing_iff_checks _ i.data read)
  have dotGate : dot = a.rhs ↔ HchecksAccumulator.ClosedSum LiteralOpeningView.eK i.data q
      (SelectedChallengeMap.rhoOf i.rho) := by
    rw [strict dot a.rhs (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]) (by simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])]
    change CheckpointBytes5Output.ofE dot = (CheckpointBytes5Output.accumulator a).rhs ↔ _
    rw [dot_S5,returned]
    simp only [OraclePortFrozen2.completeState,QueryAccumulator.run22_weights,
      QueryAccumulator.run22_rhs,HchecksAccumulator.ClosedSum]
  have normal := parent_value ops v p a alpha0 alpha1 r0 r1 weights alphas pair dot s2 ha0 ha1 hw has hp hd
  have control : (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none =
      ok (.Ok ())) ↔ ((r0.lhs = r0.rhs ∧ r1.lhs = r1.rhs ∧ pair = r1.value) ∧ dot = a.rhs) := by
    rw [normal]
    by_cases e0 : r0.lhs = r0.rhs <;> by_cases e1 : r1.lhs = r1.rhs <;>
      by_cases ep : pair = r1.value <;> by_cases ed : dot = a.rhs
    all_goals simp [e0,e1,ep,ed,next]
  have query := Port4D_FinishFrozen.query_decision i q decoded matches_S4_S7
  have checks : D0TypedChecks.verify (typedRows parsed q tr) i =
      decide (LiteralPairingChecks.checks (typedRows parsed q tr) ∧
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK i.data q (SelectedChallengeMap.rhoOf i.rho)) := by
    simp only [D0TypedChecks.verify,read]
    congr 1
    apply propext
    constructor
    · intro h
      exact ⟨h.2.1,h.2.2.2.2 q decoded⟩
    · rintro ⟨pairing,closed⟩
      refine ⟨True.intro,pairing,query,semantic_S3_S9,?_⟩
      intro q' hq'
      have eq : q' = q := Option.some.inj (hq'.symm.trans decoded)
      subst q'
      exact closed
  have sourceValue : decide (Port3_NativeFinishBody.verifier.finish_relation
      (Port4D_Round.native ops) v p a none = ok (.Ok ())) =
      D0TypedChecks.verify (typedRows parsed q tr) i := by
    rw [checks]
    exact congrArg (fun p : Prop => decide p) (propext (control.trans (and_congr gates dotGate)))
  refine ⟨?_,?_⟩
  · rw [returned,OraclePortFrozen2.finish_value parsed q tr i hi hq]
    exact sourceValue
  · have iff := Port3_QueryInstall.success_iff
      (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none) ()
    change decide (Port3_QueryInstall.result
      (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none) = ok (.Ok ())) = _
    exact (congrArg (fun p : Prop => decide p) (propext iff)).trans sourceValue

#print axioms finish_value
end AspisR1.FinT_Model
end
