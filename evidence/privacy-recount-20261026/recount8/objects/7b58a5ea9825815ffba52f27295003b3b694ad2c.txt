import R1Z.PV_RunJoin_OsTrace
import R1Z.PV_RunJoin_OsWorldFrames
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ConsumedEvent
open PV_RunJoin_OsWorld PV_RunJoin_OsTrace
variable {E File Reply Time Worker : Type} [DecidableEq File]

theorem file_append (world : World E File Reply Time Worker)
    (event : Event (Request File) Reply)
    (position : world.files[world.fileUsed]? = some event) :
    consumed ({world with fileUsed := world.fileUsed + 1}) =
      {consumed world with files := (consumed world).files ++ [event]} := by
  unfold consumed
  rw [List.take_succ,position]
  rfl

theorem time_append (world : World E File Reply Time Worker) (outcome : Time)
    (position : world.time[world.timeUsed]? = some outcome) :
    consumed ({world with timeUsed := world.timeUsed + 1}) =
      {consumed world with times := (consumed world).times ++ [outcome]} := by
  unfold consumed
  rw [List.take_succ,position]
  rfl

theorem worker_append (world : World E File Reply Time Worker) (outcome : Worker)
    (position : world.workers[world.workerUsed]? = some outcome) :
    consumed ({world with workerUsed := world.workerUsed + 1}) =
      {consumed world with workers := (consumed world).workers ++ [outcome]} := by
  unfold consumed
  rw [List.take_succ,position]
  rfl

#print axioms file_append
#print axioms time_append
#print axioms worker_append
end R1Z.PV_RunJoin_ConsumedEvent
