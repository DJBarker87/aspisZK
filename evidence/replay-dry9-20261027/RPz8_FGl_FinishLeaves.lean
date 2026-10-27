import RPz8_F3Y_FinishFields
import RPz8_F3T_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_FinishLeaves
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control

structure PairingRemaining {W : Type} (finish : FinishOps W) (v : verifier.View)
    (p : verifier.Prepared) (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) : Prop where
  round0 : Port4D_Pairing.RoundLaws (Port3_FinishStage.release finish) CheckpointBytes5Output.ofE v.round0 data.p0
  round1 : Port4D_Pairing.RoundLaws (Port3_FinishStage.release finish) CheckpointBytes5Output.ofE v.round1 data.p1
  pair : ∀ weights alphas value,
    finish.newWeights p.variant p.semantic_alpha p.z=ok (.Ok weights) →
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok alphas →
    finish.pair weights alphas v.final_message p.kappa=ok (.Ok value) →
    CheckpointBytes5Output.ofE value=RoundPairing.dot data.f
      (RoundPairing.dualFold (n:=64) data.alpha1
        (RoundPairing.dualFold (n:=256) data.alpha0 (FunctionalWeights.weights data.F data.F0 data.kappa)))

def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : SourceInputs) : Prop :=
  PairingRemaining finish v p input.data ∧
  (∀ j,MatchingSupport.match0 input.data (q j)) ∧
  R3SemanticRemainingJoins.EquationEndpoint input.decoded (typedRows parsed q tr) input.data ∧
  CheckpointBytes5Output.ofE x.dot=∑ l : Fin 64,input.data.f l *
    LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l)

theorem complete {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : SourceInputs) (fields : F3Y_FinishFields.Holds p input.data)
    (leaves : Holds finish v p a x q parsed tr input) :
    Port4D_Pairing.PairingLaws (Port3_FinishStage.release finish)
      CheckpointBytes5Output.ofE v p input.data := by
  exact ⟨leaves.1.round0,leaves.1.round1,fields.1,fields.2.1,fields.2.2,leaves.1.pair⟩

#print axioms complete
end AspisR1.FGl_FinishLeaves
end
