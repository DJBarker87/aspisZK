import FIr_SourceLast
import FIr_AlphaLiteral
import FIr_LiteralValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_LastLiteral
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun

theorem value {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (initial final : Outcome H) (entries : List (RoundEvidence D pre))
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries)
    (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre)
    (alpha : Array aspis_core.field.QM31 10#usize) (same : entries.map RoundEvidence.q=alpha.val)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (view : LiteralOpeningView.View)
    (frames : SemanticPrefixCodec.encodeFull values=LiteralSemanticCodecBridge.records (rs.take 25))
    (read : LiteralOpeningView.read rs=some view)
    (out : verifier.Prepared) (alphaSame : out.semantic_alpha=alpha)
    (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (numeric : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p data view) data.data (SelectedChallengeMap.rhoOf data.rho) q)
    (inBase : FIr_SampleRange.InBase ((view.semantic.map Prod.snd).getD 24 0))
    (polys : Fin 10 → Polynomial AspisWideTower.WideExact)
    (polyRead : R0P.Mask.semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic)=some polys) :
    (polys 9).eval ((view.semantic.map Prod.snd).getD 24 0)=
      algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact (DecodeMain final.1) := by
  have exactPolys := FIr_LiteralValues.polynomials values rs view read frames
  have polysSame := Option.some.inj (polyRead.symm.trans exactPolys)
  have challenge := FIr_AlphaLiteral.value out alpha alphaSame view p q data numeric 9 inBase
  rw [polysSame,← challenge]
  exact FIr_SourceLast.last_value run values full alpha same

#print axioms value
end AspisR1.FIr_LastLiteral
end
