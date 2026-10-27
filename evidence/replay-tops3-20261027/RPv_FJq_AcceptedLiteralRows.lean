import RPv_FJq_SourceLiteralClaims
import RPv_FJq_SourceLiteralExtra
import RPv_FJq_AcceptedExtra
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_AcceptedLiteralRows
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open FIz_ConcretePack (embed)
/-- ONE accepted semantic call supplies both Claims and extra, transported to
ONE matching reader's Y. The shared prefix parser prevents choosing rows from
another semantic execution. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std B)).op9 D pub bytes hash none=ok (.Ok sem))
    (pre : r1_wire.Prefix) (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr)
    (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows p q tr)=some data) :
    (fun j l=>embed (FJn_MainClaims.claims (retainedSem sem).claims j l))=
      (fun j l=>data.Y ⟨j.val,by omega⟩ l) ∧
    (fun l=>embed (FIp_SemanticValues.decode (FJq_MainCells.cell (retainedSem sem).extra l)))=data.Y 3 ∧
    (∀ x∈(retainedSem sem).extra.val,FIp_SemanticValues.Canon x) := by
  obtain ⟨actual,initial,after,challenges,sourceParsed,publicInit,begun,finished,claims⟩:=
    ClaimsUnrolledSdk.semantic_claims std ops B D pub bytes hash sem accepted
  have same:=core.result.Result.Ok.inj (Result.ok.inj (sourceParsed.symm.trans parsed))
  subst actual
  obtain ⟨extraPre,record,extraParsed,source,decode,canonical⟩:=
    FJq_AcceptedExtra.value std ops B D pub bytes hash sem accepted
  have same:=core.result.Result.Ok.inj (Result.ok.inj (extraParsed.symm.trans parsed))
  subst extraPre
  exact ⟨FJq_SourceLiteralClaims.value std pre (retainedSem sem).claims claims p q tr aligned records data read,
    FJq_SourceLiteralExtra.value pre record source (retainedSem sem).extra decode p q tr aligned records data read,
    canonical⟩
#print axioms value
end AspisR1.FJq_AcceptedLiteralRows
end
