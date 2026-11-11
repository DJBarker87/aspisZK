import RPx_FJt_Endpoint
import RPu_FIr_Remaining2
import RPz7_F3L_SamplerStatement
import RPv_FJt_PublicLog
import RPv_FJt_PublicJoin
import RPz7_F3M_SemanticSource
import RPv_FJq_ArbitraryChallengeLiteral
import RPv_FJq_ParsedRows
import RPv_FJq_PhysicalPrefix
import RPz7_PSem_Root
import RPz7_PAln_Physical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_RunEndpoint
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1PublicPreparation.SourceGlobalOracleInitial
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open FIz_ConcretePack (embed)
attribute [local irreducible] FIq_Terminal.terminal R0P.Mask.terminalZ

theorem value {CoreError : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo (FIq_Install.boundaries seed) std)
      reserved query geo D () pub physical proof split saved)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    (decoded : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      physical=ok (.Ok s))
    (publicSame : FirstComposition.toRetainedPublic pub=AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
    (H : Bytes → State) (backend : AspisR1PublicPreparation.Tx1DigestLog.ByteOracleBackend (retainedDigest D) H)
    (i : F3_Model.Input) (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : OraclePortStoredParserC4.parseReached (bytesOf proof.val)
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some p)
    (logs : AuS1_Recovery.log (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo)))
      (FIq_Install.boundaries seed) std D pub proof () (Array.repeat 29#usize run.zero)=
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (input : OraclePortStoredDecisionDraftC4.input p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some data) :
    FIr_Remaining2.Endpoint data.decoded (typedRows p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)) data.data := by
  let tr:=LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2
  have aligned:=(OraclePortStoredParserC4.parsed _ _ _ parsed).2.2
  obtain ⟨encoded,serialized,pubBytes⟩:=FJt_PublicLog.value _ (FIq_Install.boundaries seed) std D pub proof ()
    run.p (Array.repeat 29#usize run.zero) run.scratch run.prepare_call H i.proof i.semantic.value p aligned logs
  obtain ⟨stored,initial,expanded,y1,sourceView,sem,readStored,expand,wide,viewSame,verify,prepare⟩:=
    PSem_SourceCuts.buffers ops reserved query geo (FIq_Install.boundaries seed) std D () pub physical proof split saved run
  obtain ⟨pre,t0,t15,t25,cs,sourceParsed,publicInit,trace,order,qs,frames,circles⟩:=
    F3M_SemanticSource.values AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std (FIq_Install.boundaries seed)) D pub expanded () sem verify
  have physicalRows:=FJq_PhysicalPrefix.value proof stored initial expanded pre readStored expand sourceParsed p tr parsed
  have fields:=OraclePortStoredDecisionDraftC4.input_fields p q tr data input
  have literalPub : SemanticPublicWire.parsePublic i.semantic.value.pubBytes=some data.decoded := by
    have h:=fields.1.1
    change SemanticPublicWire.parsePublic (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2.statement.pubBytes=some data.decoded at h
    rw [F3L_SamplerStatement.statement] at h
    exact h
  have pubJoin:=FJt_PublicJoin.value (retainedDigest D) (FirstComposition.toRetainedPublic pub) s physical decoded publicSame
    () pre.c1_root t0 publicInit encoded serialized i.semantic.value data.decoded pubBytes literalPub
  have initHash : t0.hash=() := Subsingleton.elim _ _
  obtain ⟨init⟩:=public_success_has_init_call (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre.c1_root t0
    (by simpa only [initHash] using publicInit)
  have encoding : init.encoded=encoded := core.result.Result.Ok.inj (Result.ok.inj (init.serialized.symm.trans serialized))
  have initBytes : i.semantic.value.pubBytes=AspisR1PublicPreparation.SourceDigestAddresses.rawBytes init.encoded.deref := by
    rw [encoding];exact pubBytes
  have root:=PSem_Root.source_root stored initial expanded pre expand sourceParsed
  have physical:=PSem_Slices.range_bytes proof stored 16#usize 7031#usize readStored
  change stored.val=(proof.val.drop 16).take 7015 at physical
  have wire:=(parse_header _ _ (OraclePortStoredParserC4.parsed _ _ _ parsed).1).2
  have rootBytes : bytes (decodeState pre.c1_root)=root0 p := by
    rw [PAln_Physical.state_bytes,root,physical]
    simp only [root0,wire,slice,bytesOf,List.map_take,List.map_drop,List.take_take]
    rfl
  have rows:=FJq_ParsedRows.value (bytesOf proof.val) tr p parsed
  have length:=((OraclePortHeader.accepts_iff _).mp (parse_header _ _ (OraclePortStoredParserC4.parsed _ _ _ parsed).1).1).1
  rw [←wire] at length
  have bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D:=PAln_RowBounds.row_bound p rows length
  have count : cs.length=25 := by
    have h:=congrArg List.length order
    simpa only [List.length_map,List.length_range] using h
  intro v claim polys opening claimRead polyRead
  have challenges:=FJq_ArbitraryChallengeLiteral.values trace count (retainedSem sem).challenges (retainedSem sem).alpha qs
    init H backend p rows physicalRows.1 (words p q) bound i.semantic.value initBytes rootBytes i.proof aligned q v opening
  exact FJt_Endpoint.value std ops seed D pub expanded () sem pubJoin.1 verify pre sourceParsed
    (bytesOf proof.val) p q tr parsed physicalRows.1 data.data fields.2 data.decoded v opening pubJoin.2 challenges polys polyRead
#print axioms value
end AspisR1.FJt_RunEndpoint
end
