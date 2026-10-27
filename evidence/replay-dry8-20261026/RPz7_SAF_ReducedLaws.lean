import RPz7_SAF_PreparedPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_ReducedLaws
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
variable {W : Type}

/-- Exact remaining seven PairingLaws fields at the SAME Prepared, with no
strengthening of any binder or arithmetic obligation. -/
structure Arithmetic (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (d : MatchingSupport.Data AspisWideTower.WideExact) : Prop where
  round0 : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE v.round0 d.p0
  round1 : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE v.round1 d.p1
  pair : ∀ (weights : W) (alphas : Slice E) (value : E),
    ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights) →
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas →
    ops.pair weights alphas v.final_message p.kappa = ok (.Ok value) →
    CheckpointBytes5Output.ofE value = RoundPairing.dot d.f
      (RoundPairing.dualFold (n := 64) d.alpha1
        (RoundPairing.dualFold (n := 256) d.alpha0
          (FunctionalWeights.weights d.F d.F0 d.kappa)))

theorem reconstruct (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (parsed : OraclePortCompactDraft.Parsed)
    (i : RecordedBinaryExperimentBin.SourceInputs) (view : LiteralOpeningView.View)
    (q : Fin 22 → Fin 262144)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K AspisWideTower.WideExact)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context parsed i view)
        i.data (SelectedChallengeMap.rhoOf i.rho) q) am)
    (arithmetic : Arithmetic ops v p i.data) :
    Port4D_Pairing.PairingLaws ops CheckpointBytes5Output.ofE v p i.data := by
  obtain ⟨claim,a0,a1⟩ := SAF_PreparedPairing.identities p a parsed i view q am fields
  exact ⟨arithmetic.round0,arithmetic.round1,claim,a0,a1,arithmetic.pair⟩

#print axioms reconstruct
end AspisR1.SAF_ReducedLaws
end
