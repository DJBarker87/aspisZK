import RPz8_FIp_Remaining
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_Remaining2
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open R3SemanticEquationCore R3SemanticRemainingJoins

def Endpoint (pub : R0P.Public SemanticPublicWire.M31)
    (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (data : MatchingSupport.Data AspisWideTower.WideExact) : Prop :=
  ∀ (view : LiteralOpeningView.View) (claim : AspisWideTower.WideExact)
    (polys : Fin 10 → Polynomial AspisWideTower.WideExact),
    LiteralOpeningView.read rs=some view →
    R0P.Mask.claimOf (SelectedSemanticPrefixFacts.lift view.semantic)=some claim →
    R0P.Mask.semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic)=some polys →
    (polys 9).eval ((view.semantic.map Prod.snd).getD 24 0)=terminal pub view data

def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs) : Prop :=
  FIn_Finish.PairMeaning finish v p input.data ∧
  (∀ j,MatchingSupport.match0 input.data (q j)) ∧
  Endpoint input.decoded (typedRows parsed q tr) input.data
end AspisR1.FIr_Remaining2
end
