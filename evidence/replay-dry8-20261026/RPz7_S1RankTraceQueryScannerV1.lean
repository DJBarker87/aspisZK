import RPz7_S1QueryScanDriverModelV1
import RPz7_S1OriginalSerializedRankTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
noncomputable section
namespace AspisR1CurrentCaller.OriginalSerializerInstallation
open AspisR1PublicPreparation AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation.Query31SourceSchedule
open Query31ConcreteDriverTraceFacts AspisS1QueryScanModel

/-- The actual successful source query, all materialized replies, the fixed
scanner's ordered output/selected state, and rho's SAME subsequent transcript.
This is an accepted-source-model property, not a native SDK/iterator theorem. -/
def QueryScannerMeaning {H : Type} (D : aspis_core.Digest32 H)
    (v : AspisR1PublicPreparation.verifier.View) (out : AspisR1PublicPreparation.verifier.Prepared) : Prop :=
  ∃ (row : U8) (before after last absorbed : transcript.Transcript H)
    (blocks advances : Blocks8) (selected rhoBlock : Bytes32),
    ∃ pairs : List (DigestPair D absorbed.hash),
      (row=30#u8 ∨ row=31#u8) ∧
      QueriesModel.queries
        (Query31ConcreteMaterializedSchedule.concreteBoundaries sourceDefaultState AspisS1M31Embedding.Total.embed)
        D before row v.final_message=ok (.Ok out.queries,after) ∧
      transcript.Transcript.absorb D before row v.final_message=ok absorbed ∧
      materializedOutputs pairs blocks advances ∧ pairs.length=8 ∧
      after={absorbed with state:=selected} ∧
      R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
        (blocks.val.map decodeState) (advances.val.map decodeState) (decodeState absorbed.state)=
          (.ok (out.queries.val.map (fun w => w.val)),decodeState selected) ∧
      transcript.Transcript.block D after (if row=30#u8 then 31#u8 else 32#u8)
        PreparedScratchReachability.emptyPayload=ok (rhoBlock,last) ∧
      sampler.qm31_sample rhoBlock=ok out.rho ∧ out.state=last.state

theorem queryRhoFacts_scanner_meaning {H M Cv : Type} {L : Nat}
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (v : AspisR1PublicPreparation.verifier.View) (out : AspisR1PublicPreparation.verifier.Prepared)
    (row : U8) (before : transcript.Transcript H)
    (rows : row=30#u8 ∨ row=31#u8)
    (facts : ConcreteQueryRhoFacts AspisS1M31Embedding.Total.embed D p pubInput root length v out row before) :
    QueryScannerMeaning D v out := by
  obtain ⟨after,last,rhoBlock,hquery,schedule,hrho,hsample,hcanonical,hcoords,hstate⟩ := facts
  obtain ⟨absorbed,blocks,advances,selected,pairs,evidence,sf,habs,hmaterial,hlen,hstates,
    hafter,hfunctional,hchain,helen,hvalid,hwords,stopIndex,trace,hcount,hbuffer,hfinish,hadvance,hindex⟩ := schedule
  have scanned := driver_trace_scanOut blocks advances sourceDefaultState out.queries selected
    (decodeState absorbed.state) sourceDefaultState_valid rfl trace
  have model : R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
      (blocks.val.map decodeState) (advances.val.map decodeState) (decodeState absorbed.state)=
        (.ok (out.queries.val.map (fun w => w.val)),decodeState selected) := by
    simpa only [sourceDefaultState_maps_to_empty_q22,R0C.V3.Q22.q0,
      statesFrom,List.drop_zero] using scanned
  exact ⟨row,before,after,last,absorbed,blocks,advances,selected,rhoBlock,pairs,
    rows,hquery,habs,hmaterial,hlen,hafter,model,hrho,hsample,hstate⟩

/-- The pre-existing complete rank trace supplies the scanner correspondence;
no independently successful query, chosen state or decoder-value law is added. -/
theorem exactRankTrace_query_scanner {H M Cv : Type} {L : Nat}
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch : Array aspis_core.field.WideExact 29#usize)
    (trace : ExactSerializedRankTrace D p pubInput root length sem v hash out scratch) :
    QueryScannerMeaning D v out := by
  obtain ⟨start,t1,t2,t3,alpha0,gammaBlock,kappaBlock,alphaBlock,hn,hg,hgr,hk,hkr,ha,har,tail⟩ := trace
  rcases tail with single | double
  · exact queryRhoFacts_scanner_meaning D p pubInput root length v out 30#u8 t3
      (Or.inl rfl) single.2.2
  · obtain ⟨foldedRoot,bytes1,bytes2,alpha1,afterAlpha,block,hfolds,hroot,hb1,hb2,hblock,hrank,halpha,facts⟩ := double
    exact queryRhoFacts_scanner_meaning D p pubInput root length v out 31#u8 afterAlpha
      (Or.inr rfl) facts

#print axioms queryRhoFacts_scanner_meaning
#print axioms exactRankTrace_query_scanner
end AspisR1CurrentCaller.OriginalSerializerInstallation
