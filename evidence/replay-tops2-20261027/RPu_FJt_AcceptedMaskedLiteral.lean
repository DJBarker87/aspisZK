import RPu_FJt_AcceptedMaskedMain
import RPu_FJq_AcceptedLiteralRows
import RPu_FJq_MaskedLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_AcceptedMaskedLiteral
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open FIp_SemanticValues (Canon decode)
open FIz_ConcretePack (embed)
attribute [local irreducible] R0P.Mask.terminalZ
/-- Complete SAME literal masked value. Public/challenge association is the
explicit residual local join; claims, extra and all mask operands are derived. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops) (seed : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (bounds : FJa_PublicBounds.Bounds (FJa_PublicCopy.native (FirstComposition.toRetainedPublic pub)))
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std (FIq_Install.boundaries seed))).op9 D pub bytes hash none=ok (.Ok sem))
    (pre : AspisR1PublicPreparation.r1_wire.Prefix) (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr)
    (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows p q tr)=some data)
    (literalPub : R0P.Public SemanticPublicWire.M31) (v : LiteralOpeningView.View)
    (publicSame : SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic
      (FJa_PublicCopy.native (FirstComposition.toRetainedPublic pub)))=
      SpendDataMap.mapPublic ExactBaseProjection.embed literalPub)
    (challengesSame : v.semantic.map Prod.snd=FJq_ChallengeSlots.values (retainedSem sem).challenges (retainedSem sem).alpha) :
    ∃ (before after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) (running : AspisR1PublicPreparation.aspis_core.field.QM31),
      RoundModel.rounds AspisS1ExtractedRoundChildren.children (retainedDigest D) pre before=
        ok (.Ok (running,(retainedSem sem).alpha,after)) ∧
      Canon running ∧ embed (decode running)=R3SemanticRemainingJoins.terminal literalPub v data := by
  obtain ⟨actual,before,after,c,running,sourceParsed,challengeEq,rounds,can,formula⟩:=
    FJt_AcceptedMaskedMain.value std ops seed D pub bytes hash sem bounds accepted
  have same:=core.result.Result.Ok.inj (Result.ok.inj (sourceParsed.symm.trans parsed))
  subst actual
  have rows:=FJq_AcceptedLiteralRows.value std ops (FIq_Install.boundaries seed) D pub bytes hash sem accepted
    pre parsed p q tr aligned records data read
  have chosenChallenges : v.semantic.map Prod.snd=FJq_ChallengeSlots.values c (retainedSem sem).alpha := by
    rw [←challengeEq]
    exact challengesSame
  have transport:=FJq_MaskedLiteral.transport (FirstComposition.toRetainedPublic pub)
    (retainedSem sem).claims (retainedSem sem).alpha (retainedSem sem).extra c literalPub v data
    publicSame rows.1 rows.2.1 chosenChallenges
  exact ⟨before,after,running,rounds,can,formula.trans transport⟩
#print axioms value
end AspisR1.FJt_AcceptedMaskedLiteral
end
