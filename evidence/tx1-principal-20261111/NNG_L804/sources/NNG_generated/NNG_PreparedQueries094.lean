import NNG_PreparedFacts094
import NHL_QueryInterface
import F3K_SourceQueryDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedQueries094
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.Q22SamplerInvariants R0C.V3
/-- Decoder validity is independent of the transcript row number. This
uses the CLOSED concrete scanner, including duplicate rejection. -/
theorem queries_valid {H : Type} (D : aspis_core.Digest32 H)
 (before after : transcript.Transcript H) (row : U8) (payload : Slice U8)
 (out : Array U32 22#usize)
 (returned : QueriesModel.queries NGQ_TRANSCRIPT.boundaries D before row payload=ok (.Ok out,after)) :
 (out.val.map (fun x=>x.val)).Nodup ∧ ∀ x∈out.val,x.val<262144 := by
 rw [NGQ_TRANSCRIPT.adopted_boundaries] at returned
 obtain ⟨absorbed,blocks,advances,selected,_,_,decoded,_⟩ :=
  F3K_QueryDecoderSource.source _ D before after row payload out returned
 have same := F3K_ConcreteDecode.accepted blocks advances out selected (decodeState absorbed.state) decoded
 have valid := LiteralQuerySample.scanOut_result_valid 8 Q22.q0
  (blocks.val.map decodeState) (advances.val.map decodeState) (decodeState absorbed.state)
  (by simp [Valid,Q22.q0])
 rw [same] at valid
 change (out.val.map (fun x=>x.val)).Nodup ∧ (out.val.map (fun x=>x.val)).length=22 ∧
  ∀ x∈out.val.map (fun x=>x.val),x<262144 at valid
 refine ⟨valid.1,?_⟩
 intro x member
 exact valid.2.2 _ (List.mem_map.mpr ⟨x,member,rfl⟩)
#print axioms queries_valid

/-- Bounds and uniqueness belong to the SAME returned Prepared record. -/
theorem returned (input : LIBC_PreparedLaw.Args) (env : RSL.Env)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (ev : List RSL.Event)
 (success : LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),ev⟩) :
 p.queries.val.Nodup ∧ ∀ x∈p.queries.val,x.val<262144 := by
 have native := NNG_PreparedFacts094.emitted input env p g ev success
 have model := (NGN_EmittedEq.source NHL_PreparedScalars.actual (LIBC_PreparedLog.digest env)
  input.1 input.2.1 () input.2.2).symm.trans native
 rw [NHL_QueryDomain.dictionary] at model
 obtain ⟨_,_,row,before,after,last,_,query,_,_⟩ :=
  NFW_PreparedCalls.calls _ (LIBC_PreparedLog.digest env) input.1 input.2.1 () p g input.2.2 model
 change NHL_PreparedScalars.actual.sampling.queries (LIBC_PreparedLog.digest env)
  before row input.2.1.final_message=ok (.Ok p.queries,after) at query
 rw [NHL_QueryInterface.dictionary] at query
 have facts := queries_valid _ _ _ _ _ _ query
 exact ⟨List.Nodup.of_map (fun x=>x.val) facts.1,facts.2⟩
#print axioms returned
end AspisR1.NNG_PreparedQueries094
