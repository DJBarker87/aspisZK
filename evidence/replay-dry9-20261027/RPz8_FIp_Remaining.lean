import RPz8_FIn_Derived
import RPz8_FIn_Finish
import RPz8_FGl_FinishLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_Remaining
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs) : Prop :=
  FIn_Finish.PairMeaning finish v p input.data ∧
  (∀ j,MatchingSupport.match0 input.data (q j)) ∧
  R3SemanticRemainingJoins.EquationEndpoint input.decoded (typedRows parsed q tr) input.data

theorem complete {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs)
    (derived : FIn_Derived.Holds finish v p a x parsed q tr input.data)
    (remaining : Holds finish v p a x q parsed tr input) :
    FGl_FinishLeaves.Holds finish v p a x q parsed tr input :=
  ⟨⟨derived.1,derived.2.1,remaining.1⟩,remaining.2.1,remaining.2.2,derived.2.2⟩

#print axioms complete
end AspisR1.FIp_Remaining
end
