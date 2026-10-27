import RPu_FJq_ChallengeAlpha
import RPu_FIr_SourceLast
import RPu_FIr_LiteralValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_LastSource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun
open FIz_ConcretePack (embed)
/-- The final literal polynomial evaluates to the SAME source running value,
using the exact source alpha challenge and source decoded coefficients. -/
theorem value {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (before after : r1_wire.SemanticTranscript H) (running : aspis_core.field.QM31)
    (alpha : Array aspis_core.field.QM31 10#usize)
    (rounds : RoundModel.rounds AspisS1ExtractedRoundChildren.children D pre before=ok (.Ok (running,alpha,after)))
    (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (v : LiteralOpeningView.View)
    (read : LiteralOpeningView.read rs=some v)
    (frames : SemanticPrefixCodec.encodeFull values=LiteralSemanticCodecBridge.records (rs.take 25))
    (c : r1_wire.Challenges) (same : v.semantic.map Prod.snd=FJq_ChallengeSlots.values c alpha)
    (polys : Fin 10 → Polynomial AspisWideTower.WideExact)
    (polyRead : R0P.Mask.semPolysZ (SelectedSemanticPrefixFacts.lift v.semantic)=some polys) :
    (polys 9).eval ((v.semantic.map Prod.snd).getD 24 0)=embed (FIp_SemanticValues.decode running) := by
  have actual : RoundModel.rounds RawActualSemanticRoundCanonicality.actualRoundBoundaries D pre before=
      ok (.Ok (running,alpha,after)) := by rw [←FIq_SemanticSource.children_same];exact rounds
  obtain ⟨record,decoded,initial,entries,hr,hd,hi,annotated,alphaSame⟩:=
    RawActualAnnotatedChallengeSequence.rounds_success_annotated_challenges_eq_alpha D pre before after running alpha actual
  have ps:=Option.some.inj (polyRead.symm.trans (FIr_LiteralValues.polynomials values rs v read frames))
  have challenge : (v.semantic.map Prod.snd).getD 24 0=embed (FJn_MainPoint.point alpha 9) := by
    rw [same]
    exact FJq_ChallengeAlpha.value c alpha 9
  rw [ps,challenge]
  exact FIr_SourceLast.last_value annotated values full alpha alphaSame
#print axioms value
end AspisR1.FJq_LastSource
end
