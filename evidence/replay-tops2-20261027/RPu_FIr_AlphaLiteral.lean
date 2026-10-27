import RPu_FIr_ChallengeValue
import RPz7_F3L_SourcePrepared
import RPu_FIr_TranscriptRange
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_AlphaLiteral
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation

theorem value (out : verifier.Prepared) (alpha : Array aspis_core.field.QM31 10#usize)
    (same : out.semantic_alpha=alpha) (v : LiteralOpeningView.View)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (numeric : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p data v) data.data (SelectedChallengeMap.rhoOf data.rho) q)
    (j : Fin 10)
    (inBase : FIr_SampleRange.InBase ((v.semantic.map Prod.snd).getD (15+j.val) 0)) :
    algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact
      (RawActualAnnotatedPolynomialRun.DecodeMain
        (alpha.val[j.val]'(by have len := alpha.property;change alpha.val.length=10 at len;omega)))=
      (v.semantic.map Prod.snd).getD (15+j.val) 0 := by
  subst alpha
  have field := congrArg (fun z : OraclePortCheckpointAbiC5.Prepared=>z.semanticAlpha j) numeric
  change F3L_RhoMeaning.decode (F3L_SourcePrepared.semanticAlpha out j)=
    SelectedChallengeMap.rhoOf ((v.semantic.map Prod.snd).getD (15+j.val) 0) at field
  unfold F3L_SourcePrepared.semanticAlpha at field
  rw [FIr_ChallengeValue.decode_value,field]
  exact inBase

#print axioms value
end AspisR1.FIr_AlphaLiteral
end
