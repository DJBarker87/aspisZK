import R1Z.PV_RunJoin_NativeEffectInterface
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeEffectTransport
open PV_RunJoin_OsWorld PV_RunJoin_NativeEffectInterface
variable {E File Reply Time Worker : Type} [DecidableEq File]

def permitted (native : Native E File Reply Time Worker)
    (world : World E File Reply Time Worker) (request : Request File) (reply : Reply) : Prop :=
  match request with
  | .open64 path flags mode => native.open64 world path flags mode reply
  | .read owner count => native.read world owner count reply
  | .write owner bytes => native.write world owner bytes reply
  | .sync owner => native.sync world owner reply
  | .close owner => native.close world owner reply

theorem file_iff (native : Native E File Reply Time Worker) (laws : Laws E File Reply Time Worker)
    (identity : Identity native laws) (world next : World E File Reply Time Worker)
    (request : Request File) (reply : Reply) :
    (fileStep request world = some (reply,next) ∧ permitted native world request reply) ↔
      FileAllowed laws world request reply next := by
  unfold FileAllowed
  apply and_congr_right
  intro run
  cases request with
  | open64 path flags mode => exact identity.open64 world path flags mode reply next run
  | read owner count => exact identity.read world owner count reply next run
  | write owner bytes => exact identity.write world owner bytes reply next run
  | sync owner => exact identity.sync world owner reply next run
  | close owner => exact identity.close world owner reply next run

theorem time_iff (native : Native E File Reply Time Worker) (laws : Laws E File Reply Time Worker)
    (identity : Identity native laws) (world next : World E File Reply Time Worker) (outcome : Time) :
    (timeStep world = some (outcome,next) ∧ native.time world outcome) ↔ TimeAllowed laws world outcome next := by
  unfold TimeAllowed
  apply and_congr_right
  intro run
  exact identity.time world outcome next run

theorem worker_iff (native : Native E File Reply Time Worker) (laws : Laws E File Reply Time Worker)
    (identity : Identity native laws) (world next : World E File Reply Time Worker) (outcome : Worker) :
    (workerStep world = some (outcome,next) ∧ native.worker world outcome) ↔ WorkerAllowed laws world outcome next := by
  unfold WorkerAllowed
  apply and_congr_right
  intro run
  exact identity.worker world outcome next run

#print axioms file_iff
#print axioms time_iff
#print axioms worker_iff
end R1Z.PV_RunJoin_NativeEffectTransport
