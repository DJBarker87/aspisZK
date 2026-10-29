import NDH_Reference.Funs
import Query31UnrolledDriverFirstStop
set_option autoImplicit false
namespace NDH_QueryFinish
open Aeneas Aeneas.Std Result
open AspisR1Query31Transcript

def liftAnswer (r : core.result.Result (Array U32 22#usize) (Usize × Usize)) :
    core.result.Result (Array U32 22#usize) aspis_core.transcript.QuerySampleError :=
  match r with
  | .Ok a => .Ok a
  | .Err (accepted, maxDraws) => .Err (.DrawLimitExhausted accepted maxDraws)

theorem reference (s : aspis_core.r0_transcript.QueryScan) :
    (do let r ← NDH_Reference.finish_ref s.accepted s.accepted_len
        ok (liftAnswer r)) = aspis_core.r0_transcript.QueryScan.finish s := by
  simp only [NDH_Reference.finish_ref, aspis_core.r0_transcript.QueryScan.finish,
    aspis_core.r0_transcript.QUERY_COUNT, aspis_core.r0_transcript.QUERY_MAX_DRAWS]
  split <;> rfl

#print axioms reference
end NDH_QueryFinish
