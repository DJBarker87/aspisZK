import Port4D_Pairing
import Tx2N_Reader
import OraclePortAcceptedContextC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_PreparedPairing
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCheckpointResumeC5
variable {W : Type}

/-- Only the seven arithmetic families, excluding the three saved Prepared
identities. This is a visible remaining frontier, not a discharge. -/
structure Arithmetic (ops : FinishOps W) (v : verifier.View)
    (d : MatchingSupport.Data AspisWideTower.WideExact) : Prop where
  round0 : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE v.round0 d.p0
  round1 : Port4D_Pairing.RoundLaws ops CheckpointBytes5Output.ofE v.round1 d.p1
  pair : ∀ (p : verifier.Prepared) (weights : W) (alphas : Slice E) (value : E),
    ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights) →
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas →
    ops.pair weights alphas v.final_message p.kappa = ok (.Ok value) →
    CheckpointBytes5Output.ofE value = RoundPairing.dot d.f
      (RoundPairing.dualFold (n := 64) d.alpha1
        (RoundPairing.dualFold (n := 256) d.alpha0
          (FunctionalWeights.weights d.F d.F0 d.kappa)))

/-- The three non-arithmetic PairingLaws fields follow from the actual saved
checkpoint decoder's field theorem on the literal accepted Context. -/
theorem identities (p : verifier.Prepared) (a : verifier.Accumulator)
    (parsed : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (view : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K AspisWideTower.WideExact)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a
      (prepared (OraclePortAcceptedContextC6.context parsed i view) i.data
        (SelectedChallengeMap.rhoOf i.rho) q) am) :
    CheckpointBytes5Output.ofE p.claim =
      JointFunctionalBinding.claimedValue i.data.Y i.data.c0 i.data.gamma i.data.kappa ∧
    (∀ x, Array.index_usize p.alpha 0#usize = ok x → CheckpointBytes5Output.ofE x = i.data.alpha0) ∧
    (∀ x, Array.index_usize p.alpha 1#usize = ok x → CheckpointBytes5Output.ofE x = i.data.alpha1) := by
  refine ⟨?_,?_,?_⟩
  · rw [fields.claim,CheckpointBytes5Output.ofE_source]
    rfl
  · intro x hx
    have source : Array.index_usize p.alpha 0#usize =
        ok (CheckpointBytes4ReaderFields.sourceE i.data.alpha0) := by
      simp [Array.index_usize,fields.alpha,prepared]
    have eq := Result.ok.inj (hx.symm.trans source)
    rw [eq,CheckpointBytes5Output.ofE_source]
  · intro x hx
    have source : Array.index_usize p.alpha 1#usize =
        ok (CheckpointBytes4ReaderFields.sourceE i.data.alpha1) := by
      simp [Array.index_usize,fields.alpha,prepared]
    have eq := Result.ok.inj (hx.symm.trans source)
    rw [eq,CheckpointBytes5Output.ofE_source]

#print axioms identities
end AspisR1.SAF_PreparedPairing
end
