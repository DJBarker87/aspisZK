import RPz7_S1QueryEventTransportV1
import RPz7_S1RankTraceQueryScannerV1
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.OriginalSerializerInstallation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedQueryMaterialize
open AspisS1QueryProgramRelation

/-- Actual row31 and row32 calls from the SAME preparation, with the concrete
all-reply structural program relation. No independent query success premise. -/
def Row31QueryProgramMeaning {H : Type} (D : aspis_core.Digest32 H)
    (v : AspisR1PublicPreparation.verifier.View) (out : AspisR1PublicPreparation.verifier.Prepared) : Prop :=
  ∃ (before after last : transcript.Transcript H) (rhoBlock : Array U8 32#usize),
    QueriesModel.queries AspisR1CurrentCaller.BorrowedClaimPrepared.closedHashQueries
      D before 31#u8 v.final_message=ok (.Ok out.queries,after) ∧
    SameReads (AcceptedQueryRelation before.hash)
      (oracleProgram (PreparedQueryEffects.queries effects AspisR1CurrentCaller.BorrowedClaimPrepared.closedHashQueries
        D before 31#u8 v.final_message)) (fixedQuery31 before.state v.final_message) ∧
    transcript.Transcript.block D after 32#u8 PreparedScratchReachability.emptyPayload=ok (rhoBlock,last) ∧
    sampler.qm31_sample rhoBlock=ok out.rho ∧ out.state=last.state

theorem exactRankTrace_row31_program {H M Cv : Type} {L : Nat}
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared) (scratch : Array aspis_core.field.WideExact 29#usize)
    (folds : transport.Variant.folds v.variant=ok 2#usize)
    (trace : ExactSerializedRankTrace D p pubInput root length sem v hash out scratch) :
    Row31QueryProgramMeaning D v out := by
  obtain ⟨start,t1,t2,t3,alpha0,gammaBlock,kappaBlock,alphaBlock,hn,hg,hgr,hk,hkr,ha,har,tail⟩ := trace
  rcases tail with single | double
  · have neq : (2#usize : Usize)≠1#usize := by decide
    exact False.elim (neq (Result.ok.inj (folds.symm.trans single.1)))
  · obtain ⟨foldedRoot,bytes1,bytes2,alpha1,afterAlpha,block,hfolds,hroot,hb1,hb2,hblock,hrank,halpha,facts⟩ := double
    obtain ⟨after,last,rhoBlock,hquery,schedule,hrho,hsample,hcanonical,hcoords,hstate⟩ := facts
    have different : (31#u8 : U8)≠30#u8 := by decide
    simp only [if_neg different] at hrho
    exact ⟨afterAlpha,after,last,rhoBlock,hquery,
      closed_query31_same_reads p D afterAlpha v.final_message,hrho,hsample,hstate⟩

#print axioms exactRankTrace_row31_program
end AspisR1CurrentCaller.OriginalSerializerInstallation
