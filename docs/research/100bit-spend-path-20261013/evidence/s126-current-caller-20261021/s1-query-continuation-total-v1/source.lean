import S1OwnedQueryDecoderInstallationV1
import S1OwnedQueryPairsFixedModelV1
import S1QueryFinishProgramV1
set_option autoImplicit false
namespace AspisS1QueryContinuationTotal
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedQueryMaterialize
open AspisR1CurrentCaller.BorrowedClaimPrepared
abbrev Decoded := core.result.Result Query31ConcreteMaterializedSchedule.QueryOutput
  Query31ConcreteMaterializedSchedule.ScheduleQueryError

def output {H : Type} (self : transcript.Transcript H) : Decoded →
    core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H
  | .Ok (q,next) => (.Ok q,{self with state:=next})
  | .Err _ => (.Err .Transcript,self)

/-- Every post-decoder array read, field embedding and release trace call is
TOTAL. Full accepted state and native rejection mapping are explicit. -/
theorem finish_of_decoded {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (blocks advances : Blocks8) (decoded : Decoded)
    (called : closedHashQueries.decode blocks advances=ok decoded) :
    finish (M := Result) closedHashQueries D self blocks advances=ok (output self decoded) := by
  cases decoded with
  | Err e =>
    simp only [finish,called,core.result.Result.map_err,
      transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError,
      transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,bind_tc_ok,liftM,monadLift,output]
  | Ok pair =>
    rcases pair with ⟨q,next⟩
    have embedding : closedHashQueries.embed=AspisS1M31Embedding.Total.embed := rfl
    simp only [finish,called,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok,liftM,monadLift,embedding]
    rw [AspisS1QueryArrayOperations.index_total q 0#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 1#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 2#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 3#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 4#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 5#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 6#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 7#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 8#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 9#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 10#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 11#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 12#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 13#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 14#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 15#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 16#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 17#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 18#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 19#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 20#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rw [AspisS1QueryArrayOperations.index_total q 21#usize (by decide)]
    simp only [bind_tc_ok,AspisS1M31Embedding.Total.embed_total,trace.value,liftM,monadLift]
    rfl

#print axioms finish_of_decoded
end AspisS1QueryContinuationTotal
