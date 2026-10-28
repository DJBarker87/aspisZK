import NBL_QueryFinish
import NBA_QueryDriver
set_option autoImplicit false
namespace AspisR1.NBL_QueryPort
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBL_QueryDictionary
def port {H : Type} (before : transcript.Transcript H) : Result NBA_QueryDriver.Out →
    Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript H)
  | .ok (.Ok (queries,state)) => ok (.Ok queries,{before with state:=state})
  | .ok (.Err _) => ok (.Err .Transcript,before)
  | .fail e => .fail e
  | .div => .div

theorem source {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (blocks advances : NBL_QueryFinish.Blocks) (result : Result NBA_QueryDriver.Out)
    (decoded : boundaries.decode blocks advances=Query31ConcreteMaterializedSchedule.adaptScanResult result) :
    NBA_QueryFactor.finishQuery boundaries D self blocks advances=port self result := by
  cases result with
  | fail e => simp only [port,NBA_QueryFactor.finishQuery,decoded,Query31ConcreteMaterializedSchedule.adaptScanResult,bind_tc_fail]
  | div => simp only [port,NBA_QueryFactor.finishQuery,decoded,Query31ConcreteMaterializedSchedule.adaptScanResult,bind_tc_div]
  | ok inner =>
    cases inner with
    | Err e =>
      exact NBL_QueryFinish.error boundaries D self blocks advances
        (Query31ConcreteMaterializedSchedule.adaptQueryError e) decoded
    | Ok pair =>
      rcases pair with ⟨q,state⟩
      exact NBL_QueryFinish.success D self blocks advances q state decoded

#print axioms source
end AspisR1.NBL_QueryPort
