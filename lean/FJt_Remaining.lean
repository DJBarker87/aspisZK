import FIp_Remaining
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_Remaining
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
/-- The original semantic initial and adjacent equations; only terminal is omitted. -/
def Prefix (rs : LiteralAcceptanceTerminal.TranscriptRounds) : Prop :=
  ∀ (v : LiteralOpeningView.View) (claim : AspisWideTower.WideExact)
    (polys : Fin 10 → Polynomial AspisWideTower.WideExact),
    LiteralOpeningView.read rs=some v →
    R0P.Mask.claimOf (SelectedSemanticPrefixFacts.lift v.semantic)=some claim →
    R0P.Mask.semPolysZ (SelectedSemanticPrefixFacts.lift v.semantic)=some polys →
    (polys 0).eval 0+(polys 0).eval 1=claim ∧
    ∀ j : Fin 9,(polys j.succ).eval 0+(polys j.succ).eval 1=
      (polys j.castSucc).eval ((v.semantic.map Prod.snd).getD (15+j.castSucc.val) 0)

def Holds {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs) : Prop :=
  FIn_Finish.PairMeaning finish v p input.data ∧
  (∀ j,MatchingSupport.match0 input.data (q j)) ∧ Prefix (typedRows parsed q tr)

/-- Projection preserves all retained law families and their original guards. -/
theorem project {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (x : F3S_FinishWitness.Primitives finish v p a)
    (q : Fin 22 → Fin 262144) (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : RecordedBinaryExperimentBin.SourceInputs)
    (old : FIp_Remaining.Holds finish v p a x q parsed tr input) : Holds finish v p a x q parsed tr input := by
  refine ⟨old.1,old.2.1,?_⟩
  intro view claim polys opening claimRead polyRead
  have h:=old.2.2 view claim polys opening claimRead polyRead
  exact ⟨h.1,h.2.1⟩
#print axioms project
end AspisR1.FJt_Remaining
end
