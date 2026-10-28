import R1Z.PV_W_OsEntropy
import R1Z.PV_W_OsSchedule
import R1Z.PV_W_StepTransport
import R1Z.PV_W_TypedThreading
import R1Z.PV_W_ErrorSyntax
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_OsCombined
open PV_W_Threading PV_RunJoin_OsWorld PV_W_OsFile PV_W_Syntax
variable {E File Reply Time Worker Fs Allocator Extra C : Type} [DecidableEq File]

structure Data (E File Reply Time Worker Fs Allocator Extra C : Type) where
  fileUpdate : PV_W_OsFile.Update File Reply Fs Allocator Extra
  drawUpdate : PV_W_OsEntropy.Update E Fs Allocator Extra
  timeUpdate : PV_W_OsSchedule.Update Time Fs Allocator Extra
  workerUpdate : PV_W_OsSchedule.Update Worker Fs Allocator Extra
  tagFile : Request File → Reply → World E File Reply Time Worker → C
  tagDraw : Fin 128 → PV_RunJoin_CallerWorld.RawReply E → C
  tagTime : Time → World E File Reply Time Worker → C
  tagWorker : Worker → World E File Reply Time Worker → C

local notation "State" => Full E File Reply Time Worker Fs Allocator Extra
local notation "D" => Data E File Reply Time Worker Fs Allocator Extra C

def Step (d : D) (w : State) (c : Option C) (n : State) : Prop :=
  PV_W_OsFile.Step d.fileUpdate (fun q r next => some (d.tagFile q r next)) w c n ∨
  PV_W_OsEntropy.Step d.drawUpdate (fun i r => some (d.tagDraw i r)) w c n ∨
  PV_W_OsSchedule.TimeStep d.timeUpdate (fun r next => some (d.tagTime r next)) w c n ∨
  PV_W_OsSchedule.WorkerStep d.workerUpdate (fun r next => some (d.tagWorker r next)) w c n ∨
  (c = none ∧ w.os = n.os)

def OsStep (d : D) (w : World E File Reply Time Worker) (c : C)
    (n : World E File Reply Time Worker) : Prop :=
  (∃ q r, fileStep q w = some (r,n) ∧ c = d.tagFile q r n) ∨
  (∃ i : Fin 128, w.entropyUsed = i.val ∧ c = d.tagDraw i (w.entropy i) ∧
    n = {w with entropyUsed := w.entropyUsed + 1}) ∨
  (∃ r, timeStep w = some (r,n) ∧ c = d.tagTime r n) ∨
  (∃ r, workerStep w = some (r,n) ∧ c = d.tagWorker r n)

theorem silent_frame (d : D) (w n : State) (h : Step d w none n) : w.os = n.os := by
  rcases h with h | h | h | h | h
  · rcases h with ⟨q,r,next,_,bad,_⟩; cases bad
  · rcases h with ⟨i,_,bad,_⟩; cases bad
  · rcases h with ⟨r,next,_,bad,_⟩; cases bad
  · rcases h with ⟨r,next,_,bad,_⟩; cases bad
  · exact h.2

theorem visible_step (d : D) (w n : State) (c : C) (h : Step d w (some c) n) :
    OsStep d w.os c n.os := by
  rcases h with h | h | h | h | h
  · rcases h with ⟨q,r,next,matched,eq,rfl⟩
    exact Or.inl ⟨q,r,matched,Option.some.inj eq⟩
  · rcases h with ⟨i,matched,eq,rfl⟩
    exact Or.inr (Or.inl ⟨i,matched,Option.some.inj eq,rfl⟩)
  · rcases h with ⟨r,next,matched,eq,rfl⟩
    exact Or.inr (Or.inr (Or.inl ⟨r,matched,Option.some.inj eq⟩))
  · rcases h with ⟨r,next,matched,eq,rfl⟩
    exact Or.inr (Or.inr (Or.inr ⟨r,matched,Option.some.inj eq⟩))
  · cases h.1

theorem file_valid (d : D) (q : Request File) :
    Valid (Step d) (file d.fileUpdate (fun q r next => some (d.tagFile q r next)) q) :=
  PV_W_StepTransport.valid_mono _ _ (fun _ _ _ h => Or.inl h) _
    (PV_W_OsFile.file_valid _ _ q)

theorem draw_valid (d : D) (i : Fin 128) :
    Valid (Step d) (PV_W_OsEntropy.draw d.drawUpdate (fun i r => some (d.tagDraw i r)) i) :=
  PV_W_StepTransport.valid_mono _ _ (fun _ _ _ h => Or.inr (Or.inl h)) _
    (PV_W_OsEntropy.draw_valid _ _ i)

theorem time_valid (d : D) :
    Valid (Step d) (PV_W_OsSchedule.time d.timeUpdate (fun r next => some (d.tagTime r next))) :=
  PV_W_StepTransport.valid_mono _ _ (fun _ _ _ h => Or.inr (Or.inr (Or.inl h))) _
    (PV_W_OsSchedule.time_valid _ _)

theorem worker_valid (d : D) :
    Valid (Step d) (PV_W_OsSchedule.worker d.workerUpdate (fun r next => some (d.tagWorker r next))) :=
  PV_W_StepTransport.valid_mono _ _ (fun _ _ _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))) _
    (PV_W_OsSchedule.worker_valid _ _)

variable [ProverRwFull.ExternalTypes]
open ProverRwFull PV_W_TypedEffects

def reservation (a : Algebra State (Option C) Fault)
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Aeneas.Std.Array Aeneas.Std.U8 32#usize) :=
  eval (interpret a) (PV_W_ErrorSyntax.programError Fault.extraction
    (PV_W_TypedReservation.reserve self statement nonce))

/-- Conditional caller theorem for the ACTUAL reified reservation and existing
OsWorld carrier. Local model validity is not native primitive adequacy, source
helper adequacy, implicit Drop, or an Observation/D159 installation. -/
theorem reservation_full (d : D) (a : Algebra State (Option C) Fault)
    (laws : PV_W_TypedThreading.Laws a (Step d))
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (w : State) :
    Threaded (Step d) w (reservation a self statement nonce w).calls
      (reservation a self statement nonce w).world :=
  eval_valid (interpret a) (Step d) (PV_W_TypedThreading.primitive_valid a (Step d) laws) _ w

theorem reservation_os (d : D) (a : Algebra State (Option C) Fault)
    (laws : PV_W_TypedThreading.Laws a (Step d))
    (self : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (statement nonce : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (w : State) :
    Threaded (OsStep d) w.os
      (PV_W_Enriched.projectTrace PV_W_Enriched.World.os
        (reservation a self statement nonce w).calls)
      (reservation a self statement nonce w).world.os :=
  PV_W_Enriched.project_threaded PV_W_Enriched.World.os (Step d) (OsStep d)
    (silent_frame d) (visible_step d) (reservation_full d a laws self statement nonce w)

#print axioms silent_frame
#print axioms visible_step
#print axioms file_valid
#print axioms draw_valid
#print axioms time_valid
#print axioms worker_valid
#print axioms reservation_full
#print axioms reservation_os
end R1Z.PV_W_OsCombined
