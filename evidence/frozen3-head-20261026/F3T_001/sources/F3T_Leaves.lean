import F3S_AcceptanceValues
import F3S_FinishUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Leaves
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control

/-- These are precisely the still-retained finish owner leaves, indexed by
actual primitive results. This definition does not assert their inhabitation. -/
def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : SourceInputs) : Prop :=
  Port4D_Pairing.PairingLaws (Port3_FinishStage.release finish)
    CheckpointBytes5Output.ofE v p input.data ∧
  (∀ j, MatchingSupport.match0 input.data (q j)) ∧
  R3SemanticRemainingJoins.EquationEndpoint input.decoded (typedRows parsed q tr) input.data ∧
  CheckpointBytes5Output.ofE x.dot = ∑ l : Fin 64, input.data.f l *
    LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l) ∧
  (∀ y ∈ [x.r0.lhs,x.r0.rhs,x.r1.lhs,x.r1.rhs,x.pair,x.r1.value,x.dot,a.rhs],
    CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE y) = y)

/-- Non-vacuous use of Values needs leaves at the SAME actual primitives.
The existential primitive witness inside Values cannot choose a different dot. -/
theorem apply_values {W : Type} (finish : FinishOps W) (v : verifier.View)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (H : Bytes → State) (trace : List (Bytes × State))
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : SourceInputs) (decoder : LiteralByteProtocol.Decoder) (modelInput : F3_Model.Input)
    (x : F3S_FinishWitness.Primitives finish v p a)
    (leaves : Holds finish v p a x q parsed tr input)
    (values : F3S_AcceptanceValues.Values finish v p a H trace parsed q tr input decoder modelInput) :
    AuS1_Finish.Collision H trace parsed q ∨
      (AspisV8R19.MemoizedProgramLaw.eval H (F3_Model.verifier decoder modelInput)).2=true := by
  obtain ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd,cont⟩ := values
  let y : F3S_FinishWitness.Primitives finish v p a :=
    ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd⟩
  have same := F3S_FinishUnique.unique finish v p a x y
  have atY : Holds finish v p a y q parsed tr input := same ▸ leaves
  exact cont atY.1 atY.2.1 atY.2.2.1 atY.2.2.2.1 atY.2.2.2.2
#print axioms apply_values
end AspisR1.F3T_Leaves
end
