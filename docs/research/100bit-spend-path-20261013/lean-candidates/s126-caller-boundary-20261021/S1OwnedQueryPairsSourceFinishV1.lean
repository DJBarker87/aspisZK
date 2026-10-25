import S1OwnedQueryPairsFinishModelV1
import S1OwnedQueryPairsSourceStepV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result
abbrev OldError := AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError
abbrev OldResult := core.result.Result ((Array U32 22#usize) × Block) OldError

def toOldError : SampleError → OldError
  | .BoundNotPowerOfTwo bound => .BoundNotPowerOfTwo bound
  | .CountExceedsBound count bound => .CountExceedsBound count bound
  | .DrawLimitExhausted accepted maximum => .DrawLimitExhausted accepted maximum

def toOldResult : NativeResult → OldResult
  | .Ok value => .Ok value
  | .Err e => .Err (toOldError e)

def adapt (r : Result NativeResult) : Result OldResult := do
  let value ← r
  ok (toOldResult value)

/-- Full native error/state preserving finisher equality; source advance
index totality removes the ordering difference even on rejection. -/
theorem finish_source (s : OwnedScan) (advances : Blocks) (k : Usize) (bound : k.val<8) :
    AspisR1Query31Transcript.finishAdvance advances k (project s)=
      adapt (pairs_finish s (atBlock advances k bound)) := by
  unfold AspisR1Query31Transcript.finishAdvance
    AspisR1Query31Transcript.aspis_core.r0_transcript.QueryScan.finish
    AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_COUNT
    AspisR1Query31Transcript.aspis_core.r0_transcript.QUERY_MAX_DRAWS
    project adapt pairs_finish
  by_cases full : s.accepted_len=22#usize
  · simp only [if_pos full,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      atBlock_call advances k bound,toOldResult]
  · simp only [if_neg full,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from,toOldResult,toOldError]

#print axioms finish_source
end AspisS1OwnedQueryPairs.Model
