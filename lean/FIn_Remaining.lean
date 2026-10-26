import FIn_Derived
import FIn_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Remaining
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs) : Prop :=
  FIn_Finish.PairMeaning finish v p input.data ∧
  (∀ j,MatchingSupport.match0 input.data (q j)) ∧
  R3SemanticRemainingJoins.EquationEndpoint input.decoded (typedRows parsed q tr) input.data ∧
  (∀ y∈[x.r0.lhs,x.r0.rhs,x.r1.lhs,x.r1.rhs,x.pair,x.r1.value,x.dot,a.rhs],
    CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE y)=y)

theorem complete {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs)
    (derived : FIn_Derived.Holds finish v p a x parsed q tr input.data)
    (remaining : Holds finish v p a x q parsed tr input) :
    F3Y_FinishLeaves.Holds finish v p a x q parsed tr input :=
  ⟨⟨derived.1,derived.2.1,remaining.1⟩,remaining.2.1,remaining.2.2.1,derived.2.2,remaining.2.2.2⟩

#print axioms complete
end AspisR1.FIn_Remaining
end
