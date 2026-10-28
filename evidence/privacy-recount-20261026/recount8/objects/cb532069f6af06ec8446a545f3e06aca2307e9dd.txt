import R1Z.PV_RunJoin_OsWorld
set_option autoImplicit false
namespace R1Z.PV_RunJoin_OsWorldFrames
open PV_RunJoin_OsWorld
variable {E File Reply Time Worker : Type} [DecidableEq File]

/-- Consuming a filesystem event cannot reset or redraw the entropy tape;
time and scheduling remain separate event inputs. -/
theorem file_frame (request : Request File) (world next : World E File Reply Time Worker)
    (reply : Reply) (run : fileStep request world = some (reply,next)) :
    next.entropy = world.entropy ∧ next.entropyUsed = world.entropyUsed ∧
    next.time = world.time ∧ next.timeUsed = world.timeUsed ∧
    next.workers = world.workers ∧ next.workerUsed = world.workerUsed ∧
    next.fileUsed = world.fileUsed + 1 := by
  unfold fileStep at run
  cases position : world.files[world.fileUsed]? with
  | none => simp [position] at run
  | some event =>
    simp only [position] at run
    dsimp only [Bind.bind,Option.bind] at run
    split at run
    · cases Option.some.inj run
      exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · contradiction

theorem time_frame (world next : World E File Reply Time Worker)
    (outcome : Time) (run : timeStep world = some (outcome,next)) :
    next.entropy = world.entropy ∧ next.entropyUsed = world.entropyUsed ∧
    next.files = world.files ∧ next.fileUsed = world.fileUsed ∧
    next.workers = world.workers ∧ next.workerUsed = world.workerUsed ∧
    next.timeUsed = world.timeUsed + 1 := by
  unfold timeStep at run
  cases position : world.time[world.timeUsed]? with
  | none => simp [position] at run
  | some value =>
    simp only [position] at run
    dsimp only [Bind.bind,Option.bind] at run
    cases Option.some.inj run
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem worker_frame (world next : World E File Reply Time Worker)
    (outcome : Worker) (run : workerStep world = some (outcome,next)) :
    next.entropy = world.entropy ∧ next.entropyUsed = world.entropyUsed ∧
    next.files = world.files ∧ next.fileUsed = world.fileUsed ∧
    next.time = world.time ∧ next.timeUsed = world.timeUsed ∧
    next.workerUsed = world.workerUsed + 1 := by
  unfold workerStep at run
  cases position : world.workers[world.workerUsed]? with
  | none => simp [position] at run
  | some value =>
    simp only [position] at run
    dsimp only [Bind.bind,Option.bind] at run
    cases Option.some.inj run
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms file_frame
#print axioms time_frame
#print axioms worker_frame
end R1Z.PV_RunJoin_OsWorldFrames
