import FJq_AcceptedLiteralRows
import FJq_PhysicalPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_OnRunLiteralRows
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open FIz_ConcretePack (embed)
/-- Actual TX1 source run produces the semantic object and its original
preparation, with all Claims/extra coordinates equal to the SAME literal Y. -/
theorem value {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (parsed : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr=some p)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows p q tr)=some data) :
    ∃ (expanded y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      sourceView proof expanded y1=ok (.Ok view) ∧ view.semantic=expanded ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        D sem view hash (Array.repeat 29#usize run.zero)=ok (.Ok run.p,run.scratch) ∧
      (fun j l=>embed (FJn_MainClaims.claims (retainedSem sem).claims j l))=
        (fun j l=>data.Y ⟨j.val,by omega⟩ l) ∧
      (fun l=>embed (FIp_SemanticValues.decode (FJq_MainCells.cell (retainedSem sem).extra l)))=data.Y 3 ∧
      (∀ x∈(retainedSem sem).extra.val,FIp_SemanticValues.Canon x) := by
  obtain ⟨stored,initial,expanded,y1,view,sem,rstored,expand,wide,same,verify,prepare⟩:=
    PSem_SourceCuts.buffers ops reserved query geo B std D hash pub publicBytes proof split saved run
  obtain ⟨pre,t0,t15,c,sourceParsed,publicInit,begin,finish,claims⟩:=
    ClaimsUnrolledSdk.semantic_claims std ops B D pub expanded hash sem verify
  have physical:=FJq_PhysicalPrefix.value proof stored initial expanded pre rstored expand sourceParsed p tr parsed
  have values:=FJq_AcceptedLiteralRows.value std ops B D pub expanded hash sem verify pre sourceParsed
    p q tr physical.2 physical.1 data read
  exact ⟨expanded,y1,view,sem,wide,same,verify,prepare,values.1,values.2.1,values.2.2⟩
#print axioms value
end AspisR1.FJq_OnRunLiteralRows
end
