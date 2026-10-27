import FIp_Remaining
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_Remaining
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
/-- Identical retained pair and semantic families; matching is derived locally. -/
def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs) : Prop :=
  FIn_Finish.PairMeaning finish v p input.data ∧
  R3SemanticRemainingJoins.EquationEndpoint input.decoded (typedRows parsed q tr) input.data

theorem complete {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs)
    (remaining : Holds finish v p a x q parsed tr input)
    (matched : ∀ j, MatchingSupport.match0 input.data (q j)) :
    FIp_Remaining.Holds finish v p a x q parsed tr input := ⟨remaining.1,matched,remaining.2⟩
#print axioms complete
end AspisR1.FJp_Remaining
end
