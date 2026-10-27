import R1Z.PV_OptB_OsDeterminism
set_option autoImplicit false
namespace R1Z.PV_OptB_WorldFrames
open PV_RunJoin_OsWorld
variable {E File Reply Time Worker : Type}

/-- The immutable OS input tapes; all four changing cursors are retained in
World. This projection is only a frame invariant, never an observer rewrite. -/
def tapes (w : World E File Reply Time Worker) :=
  (w.entropy,w.files,w.time,w.workers)

/-- All reached positions are visible in the proof interface. -/
def cursors (w : World E File Reply Time Worker) :=
  (w.entropyUsed,w.fileUsed,w.timeUsed,w.workerUsed)

#print axioms tapes
#print axioms cursors
theorem file_frame [DecidableEq File] (w next : World E File Reply Time Worker)
    (request : Request File) (reply : Reply) (called : fileStep request w = some (reply,next)) :
    tapes next = tapes w := by
  unfold fileStep at called
  cases found : w.files[w.fileUsed]? with
  | none => simp [found] at called
  | some event =>
    simp [found] at called
    rcases called with ⟨_,_,rfl⟩
    rfl

#print axioms file_frame
theorem time_frame (w next : World E File Reply Time Worker)
    (reply : Time) (called : timeStep w = some (reply,next)) : tapes next = tapes w := by
  unfold timeStep at called
  cases found : w.time[w.timeUsed]? with
  | none => simp [found] at called
  | some event => simp [found] at called; rcases called with ⟨_,rfl⟩; rfl

#print axioms time_frame
theorem worker_frame (w next : World E File Reply Time Worker)
    (reply : Worker) (called : workerStep w = some (reply,next)) : tapes next = tapes w := by
  unfold workerStep at called
  cases found : w.workers[w.workerUsed]? with
  | none => simp [found] at called
  | some event => simp [found] at called; rcases called with ⟨_,rfl⟩; rfl

#print axioms worker_frame
theorem file_cursor [DecidableEq File] (w next : World E File Reply Time Worker)
    (request : Request File) (reply : Reply) (called : fileStep request w = some (reply,next)) :
    cursors next = (w.entropyUsed,w.fileUsed+1,w.timeUsed,w.workerUsed) := by
  unfold fileStep at called
  cases found : w.files[w.fileUsed]? with
  | none => simp [found] at called
  | some event =>
    simp [found] at called
    rcases called with ⟨_,_,rfl⟩
    rfl

#print axioms file_cursor
theorem time_cursor (w next : World E File Reply Time Worker)
    (reply : Time) (called : timeStep w = some (reply,next)) :
    cursors next = (w.entropyUsed,w.fileUsed,w.timeUsed+1,w.workerUsed) := by
  unfold timeStep at called
  cases found : w.time[w.timeUsed]? with
  | none => simp [found] at called
  | some event => simp [found] at called; rcases called with ⟨_,rfl⟩; rfl

#print axioms time_cursor
theorem worker_cursor (w next : World E File Reply Time Worker)
    (reply : Worker) (called : workerStep w = some (reply,next)) :
    cursors next = (w.entropyUsed,w.fileUsed,w.timeUsed,w.workerUsed+1) := by
  unfold workerStep at called
  cases found : w.workers[w.workerUsed]? with
  | none => simp [found] at called
  | some event => simp [found] at called; rcases called with ⟨_,rfl⟩; rfl

#print axioms worker_cursor
theorem time_unique (laws : Laws E File Reply Time Worker)
    (w a b : World E File Reply Time Worker) (left right : Time)
    (hl : TimeAllowed laws w left a) (hr : TimeAllowed laws w right b) : left = right ∧ a = b := by
  exact Prod.mk.inj (Option.some.inj (hl.1.symm.trans hr.1))

#print axioms time_unique
theorem worker_unique (laws : Laws E File Reply Time Worker)
    (w a b : World E File Reply Time Worker) (left right : Worker)
    (hl : WorkerAllowed laws w left a) (hr : WorkerAllowed laws w right b) : left = right ∧ a = b := by
  exact Prod.mk.inj (Option.some.inj (hl.1.symm.trans hr.1))

#print axioms worker_unique
theorem world_ext (w u : World E File Reply Time Worker)
    (same_tapes : tapes w = tapes u) (same_cursors : cursors w = cursors u) : w = u := by
  cases w; cases u
  simp only [tapes,Prod.mk.injEq,cursors] at same_tapes same_cursors
  rcases same_tapes with ⟨h1,h2,h3,h4⟩
  rcases same_cursors with ⟨h5,h6,h7,h8⟩
  subst_vars
  rfl

#print axioms world_ext
theorem flush_tapes (w : World E File Reply Time Worker) : tapes (flush w) = tapes w := rfl

#print axioms flush_tapes
theorem flush_cursors (w : World E File Reply Time Worker) : cursors (flush w) = cursors w := rfl

#print axioms flush_cursors
end R1Z.PV_OptB_WorldFrames
