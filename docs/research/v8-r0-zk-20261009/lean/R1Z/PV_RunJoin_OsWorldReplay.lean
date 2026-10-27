import R1Z.PV_RunJoin_OsWorldFrames
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OsWorldReplay
open PV_RunJoin_OsWorld
variable {E File Reply Time Worker : Type} [DecidableEq File]
local notation "State" => World E File Reply Time Worker

inductive Step : State → State → Prop where
  | file (request : Request File) (reply : Reply) (s t : State)
      (run : fileStep request s = some (reply,t)) : Step s t
  | time (outcome : Time) (s t : State)
      (run : timeStep s = some (outcome,t)) : Step s t
  | worker (outcome : Worker) (s t : State)
      (run : workerStep s = some (outcome,t)) : Step s t

inductive Replay : State → State → Prop where
  | refl (s : State) : Replay s s
  | tail (s t u : State) (prior : Replay s t) (step : Step t u) : Replay s u

theorem step_entropy {s t : State} (step : Step s t) :
    t.entropy = s.entropy ∧ t.entropyUsed = s.entropyUsed := by
  cases step with
  | file request reply s t run =>
    have frame := PV_RunJoin_OsWorldFrames.file_frame request s t reply run
    exact ⟨frame.1,frame.2.1⟩
  | time outcome s t run =>
    have frame := PV_RunJoin_OsWorldFrames.time_frame s t outcome run
    exact ⟨frame.1,frame.2.1⟩
  | worker outcome s t run =>
    have frame := PV_RunJoin_OsWorldFrames.worker_frame s t outcome run
    exact ⟨frame.1,frame.2.1⟩

theorem replay_entropy {s t : State} (run : Replay s t) :
    t.entropy = s.entropy ∧ t.entropyUsed = s.entropyUsed := by
  induction run with
  | refl => exact ⟨rfl,rfl⟩
  | tail t u prior step ih =>
    have frame := step_entropy step
    exact ⟨frame.1.trans ih.1,frame.2.trans ih.2⟩

#print axioms step_entropy
#print axioms replay_entropy
end R1Z.PV_RunJoin_OsWorldReplay
