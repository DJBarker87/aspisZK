import NBL_ContinuationHash
import NBL_OpeningHashReplay
import NBL_QueryHashReplay
set_option autoImplicit false
namespace AspisR1.NBL_PrepareHashReject
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode

/-- Query rejection on ONE opening/query trace. The log ends after all eager
query reads and scratch stays old; no rho/powers/claim suffix is invented. -/
theorem source {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (old : NBL_PrepareControl.Scratch) (opening : NBL_OpeningTrace.Trace D sem v hash)
    (queries : NBL_QueryTrace.Trace D opening.alpha1.block.after 31#u8 v.final_message)
    (error : AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError)
    (rejected : queries.result=ok (.Err error)) :
    run (NBL_CohortCode.code D sem v hash old)=
      (NBL_HashReplay.events D hash (opening.log++NBL_QueryHashReplay.log queries),
        ok (.Err .Transcript,old)) := by
  let C := preparationEffects NBA_Installed.actual NBL_QueryDictionary.boundaries
  have queryRun := NBL_QueryHashReplay.source D opening.alpha1.block.after 31#u8 v.final_message queries
  rw [rejected] at queryRun
  have tail := NBL_ContinuationHash.query_error C D sem v old opening.output
    (NBL_HashReplay.events D hash (NBL_QueryHashReplay.log queries)) .Transcript
    queries.afterAbsorb queryRun
  have whole := NBL_ContinuationHash.after_opening C D sem v hash old opening.output
    (NBL_HashReplay.events D hash opening.log)
    (NBL_HashReplay.events D hash (NBL_QueryHashReplay.log queries)) _
    (NBL_OpeningHashReplay.source D sem v hash opening) tail
  simpa only [NBL_CohortCode.code,NBL_HashReplay.events,List.map_append] using whole

#print axioms source
end AspisR1.NBL_PrepareHashReject
