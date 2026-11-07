import PV_FN_THREAD_f6RequestStack
set_option autoImplicit false
namespace PV_FN_THREAD_f6RequestQuiet
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Non-success return propagation does not execute any saved caller's next
instruction, including when that arbitrary caller has a retained request. -/
def Quiet : Status → Prop
  | .running c => ∃ r, c.frame.completed = some r ∧ (∀ value, r ≠ .ok value)
  | .returned r _ => ∀ value, r ≠ .ok value
  | .fault _ _ => True
  | .undefined _ _ => True

/-- A non-success full reply remains non-success during source restoration.
This does not reclassify divergence as a successful return or drop its store. -/
theorem delivered {W E : Type} (B : Carrier W Data) (c : Config)
    (wait : PV_STX2_Native.Waiting Data) (r : Result Data) (w : W)
    (nonok : ∀ value, r ≠ .ok value) :
    Quiet (PV_STX2_SliceMachine.adopt c c.frame.remaining
      (PV_STX2_Pinned.reply B (native c []) wait (⟨.returned r,w,[]⟩ : Reply W E Data))).status := by
  cases r with
  | ok value => exact False.elim (nonok value rfl)
  | fail err =>
    simp only [PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
      PV_STX2_SliceMachine.adopt]
    cases c.callers with
    | nil => intro value h; cases h
    | cons f rest => exact ⟨.fail err,rfl,by intro value h; cases h⟩
  | div =>
    simp only [PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,
      PV_STX2_SliceMachine.adopt]
    cases c.callers with
    | nil => intro value h; cases h
    | cons f rest => exact ⟨.div,rfl,by intro value h; cases h⟩

/-- Source completion of a fail/div result is request-free even below the
original return boundary. This closes the error-propagation control case of
the request inventory induction without imposing a condition on lower callers. -/
theorem source_step {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (quiet : Quiet (.running c)) :
    Quiet (PV_STX2_SliceMachine.step B K P H c w).status := by
  rcases quiet with ⟨r,done,nonok⟩
  unfold PV_STX2_SliceMachine.step
  simp only [done]
  cases callers : c.callers with
  | nil => exact nonok
  | cons parent rest =>
    cases waiting : parent.waiting with
    | none => simp [waiting,Quiet]
    | some wait =>
      simp only [waiting]
      exact delivered B ⟨parent,rest,c.store⟩ wait r w nonok

/-- Native reply delivery never terminates with an Ok result: success resumes
the waiting frame, while non-success answers retain their own result/fault. -/
theorem pinned_no_ok {W E : Type} (B : Carrier W Data)
    (c : PV_STX2_Native.Config Data) (wait : PV_STX2_Native.Waiting Data)
    (r : Reply W E Data) (value : Data) :
    (PV_STX2_Pinned.reply B c wait r).status ≠ .returned (.ok value) := by
  cases answer : r.answer with
  | pending => simp [PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
      PV_STX2_Native.reply,answer]
  | fault f =>
    cases f <;> simp [PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
      PV_STX2_Pinned.eraseFault,PV_STX2_PinnedConfig,PV_STX2_Native.reply,answer]
  | returned result =>
    cases result with
    | fail err => simp [PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
        PV_STX2_Native.reply,answer]
    | div => simp [PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
        PV_STX2_Native.reply,answer]
    | ok v =>
      simp only [PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
        PV_STX2_Native.reply,answer]
      split <;> simp

/-- A source return with a saved caller marks completion instead of escaping
as a terminal Ok. This is the reason an intrinsic caller cannot resume inside
the provider's pre-restoration request-coverage induction. -/
theorem adopt_no_ok {W E : Type} (c : Config)
    (rest : List PV_STX2_SliceSyntax.Node) (p : PV_STX2_Native.Prefix W E Data)
    (saved : c.callers ≠ []) (value : Data) (store : Store Data) :
    (PV_STX2_SliceMachine.adopt c rest p).status ≠ .returned (.ok value) store := by
  cases status : p.status with
  | running next => simp [PV_STX2_SliceMachine.adopt,status]
  | fault f => simp [PV_STX2_SliceMachine.adopt,status]
  | undefined site => simp [PV_STX2_SliceMachine.adopt,status]
  | returned r =>
    cases callers : c.callers with
    | nil => exact False.elim (saved callers)
    | cons parent more => simp [PV_STX2_SliceMachine.adopt,status,callers]

#print axioms pinned_no_ok
#print axioms adopt_no_ok
#print axioms delivered
#print axioms source_step
end PV_FN_THREAD_f6RequestQuiet
