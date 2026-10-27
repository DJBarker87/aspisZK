from step import check,append
m='R1Z/PV_OptB_WorldFrames';ns='R1Z.PV_OptB_WorldFrames'
check(m)
for name,body in [
('file_frame','''theorem file_frame [DecidableEq File] (w next : World E File Reply Time Worker)
    (request : Request File) (reply : Reply) (called : fileStep request w = some (reply,next)) :
    tapes next = tapes w := by
  unfold fileStep at called
  cases at : w.files[w.fileUsed]? with
  | none => simp only [at,Option.bind_none] at called; cases called
  | some event =>
    simp only [at,Option.bind_some] at called
    split at called
    · cases called; rfl
    · cases called
'''),
('time_frame','''theorem time_frame (w next : World E File Reply Time Worker)
    (reply : Time) (called : timeStep w = some (reply,next)) : tapes next = tapes w := by
  unfold timeStep at called
  cases at : w.time[w.timeUsed]? with
  | none => simp only [at,Option.bind_none] at called; cases called
  | some event => simp only [at,Option.bind_some] at called; cases called; rfl
'''),
('worker_frame','''theorem worker_frame (w next : World E File Reply Time Worker)
    (reply : Worker) (called : workerStep w = some (reply,next)) : tapes next = tapes w := by
  unfold workerStep at called
  cases at : w.workers[w.workerUsed]? with
  | none => simp only [at,Option.bind_none] at called; cases called
  | some event => simp only [at,Option.bind_some] at called; cases called; rfl
'''),
('file_cursor','''theorem file_cursor [DecidableEq File] (w next : World E File Reply Time Worker)
    (request : Request File) (reply : Reply) (called : fileStep request w = some (reply,next)) :
    cursors next = (w.entropyUsed,w.fileUsed+1,w.timeUsed,w.workerUsed) := by
  unfold fileStep at called
  cases at : w.files[w.fileUsed]? with
  | none => simp only [at,Option.bind_none] at called; cases called
  | some event =>
    simp only [at,Option.bind_some] at called
    split at called
    · cases called; rfl
    · cases called
'''),
('time_cursor','''theorem time_cursor (w next : World E File Reply Time Worker)
    (reply : Time) (called : timeStep w = some (reply,next)) :
    cursors next = (w.entropyUsed,w.fileUsed,w.timeUsed+1,w.workerUsed) := by
  unfold timeStep at called
  cases at : w.time[w.timeUsed]? with
  | none => simp only [at,Option.bind_none] at called; cases called
  | some event => simp only [at,Option.bind_some] at called; cases called; rfl
'''),
('worker_cursor','''theorem worker_cursor (w next : World E File Reply Time Worker)
    (reply : Worker) (called : workerStep w = some (reply,next)) :
    cursors next = (w.entropyUsed,w.fileUsed,w.timeUsed,w.workerUsed+1) := by
  unfold workerStep at called
  cases at : w.workers[w.workerUsed]? with
  | none => simp only [at,Option.bind_none] at called; cases called
  | some event => simp only [at,Option.bind_some] at called; cases called; rfl
'''),
('time_unique','''theorem time_unique (laws : Laws E File Reply Time Worker)
    (w a b : World E File Reply Time Worker) (left right : Time)
    (hl : TimeAllowed laws w left a) (hr : TimeAllowed laws w right b) : left = right ∧ a = b := by
  exact Prod.mk.inj (Option.some.inj (hl.1.symm.trans hr.1))
'''),
('worker_unique','''theorem worker_unique (laws : Laws E File Reply Time Worker)
    (w a b : World E File Reply Time Worker) (left right : Worker)
    (hl : WorkerAllowed laws w left a) (hr : WorkerAllowed laws w right b) : left = right ∧ a = b := by
  exact Prod.mk.inj (Option.some.inj (hl.1.symm.trans hr.1))
'''),
('world_ext','''theorem world_ext (w u : World E File Reply Time Worker)
    (same_tapes : tapes w = tapes u) (same_cursors : cursors w = cursors u) : w = u := by
  cases w; cases u
  simp only [tapes,Prod.mk.injEq,cursors] at same_tapes same_cursors
  rcases same_tapes with ⟨h1,h2,h3,h4⟩
  rcases same_cursors with ⟨h5,h6,h7,h8⟩
  subst_vars
  rfl
'''),
('flush_tapes','''theorem flush_tapes (w : World E File Reply Time Worker) : tapes (flush w) = tapes w := rfl
'''),
('flush_cursors','''theorem flush_cursors (w : World E File Reply Time Worker) : cursors (flush w) = cursors w := rfl
''')]:append(m,ns,name,body)
