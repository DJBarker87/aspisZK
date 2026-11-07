import PV_FN_THREAD_f6ProviderRequestOrigins
set_option autoImplicit false
namespace PV_FN_THREAD_f6RequestStep
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store

/-- Instructions that cannot introduce a request outside the selected emitted
call inventory. Cleanup is empty in all six inventoried provider bodies. -/
def InstructionAllowed (allowed : Data → Prop) : Instruction → Prop
  | .storage _ _ _ => True
  | .bind _ _ _ => True
  | .aggregateMove _ _ _ _ => True
  | .ret _ _ => True
  | .call _ fn _ _ cleanup => allowed fn ∧ cleanup = []
  | _ => False

def WaitingAllowed (allowed : Data → Prop) (wait : PV_STX2_Native.Waiting Data) : Prop :=
  (∃ fn a args, wait.request = .child fn a args ∧ allowed fn) ∧ wait.unwind = []

def NativeAllowed (allowed : Data → Prop) (c : PV_STX2_Native.Config Data) : Prop :=
  (∀ i ∈ c.remaining, InstructionAllowed allowed i) ∧
  (∀ wait, c.waiting = some wait → WaitingAllowed allowed wait)

/-- Arbitrary complete replies cannot manufacture a new native request. Pending
keeps the original request; success clears it; all other answers retain their
actual terminal branch. Empty cleanup is derived from emitted syntax. -/
theorem reply {W E : Type} (B : Carrier W Data) (allowed : Data → Prop)
    (c : PV_STX2_Native.Config Data) (wait : PV_STX2_Native.Waiting Data)
    (r : Reply W E Data) (safe : NativeAllowed allowed c)
    (cleanup : wait.unwind = []) :
    ∀ d, (PV_STX2_Native.reply B c wait r).status = .running d →
      NativeAllowed allowed d := by
  intro d eq
  cases answer : r.answer with
  | pending =>
    simp only [PV_STX2_Native.reply,answer] at eq
    cases eq
    exact safe
  | fault f =>
    cases f <;> simp [PV_STX2_Native.reply,answer,cleanup] at eq
  | returned result =>
    cases result with
    | fail err => simp [PV_STX2_Native.reply,answer] at eq
    | div => simp [PV_STX2_Native.reply,answer] at eq
    | ok value =>
      simp only [PV_STX2_Native.reply,answer] at eq
      split at eq
      · cases eq
        exact ⟨safe.1,by intro wait h; cases h⟩
      · cases eq

/-- One native transition preserves the runtime request inventory, for arbitrary
operand evaluation, arbitrary stores and every full reply. This is a control
provenance result; it imposes no value or world equality. -/
theorem step {W E : Type} (B : Carrier W Data)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (allowed : Data → Prop) (c : PV_STX2_Native.Config Data) (w : W)
    (safe : NativeAllowed allowed c) :
    ∀ d, (PV_STX2_Native.step B H c w).status = .running d → NativeAllowed allowed d := by
  intro d eq
  cases waiting : c.waiting with
  | some wait =>
    simp only [PV_STX2_Native.step,waiting] at eq
    exact reply B allowed c wait _ safe (safe.2 wait waiting).2 d eq
  | none =>
    cases remaining : c.remaining with
    | nil => simp [PV_STX2_Native.step,waiting,remaining] at eq
    | cons i rest =>
      have head := safe.1 i (by rw [remaining]; exact List.mem_cons_self)
      have tail : ∀ j ∈ rest, InstructionAllowed allowed j := by
        intro j member
        exact safe.1 j (by rw [remaining]; exact List.mem_cons_of_mem _ member)
      cases i with
      | storage site live n =>
        simp only [PV_STX2_Native.step,waiting,remaining] at eq
        cases eq
        exact ⟨tail,by intro wait h; cases h⟩
      | bind site dest expression =>
        simp only [PV_STX2_Native.step,waiting,remaining] at eq
        split at eq
        · cases eq
        · cases eq
          exact ⟨tail,by intro wait h; cases h⟩
      | aggregateMove site dest tag captures =>
        simp only [PV_STX2_Native.step,waiting,remaining] at eq
        split at eq
        · cases eq
        · cases eq
          exact ⟨tail,by intro wait h; cases h⟩
      | call site fn args dest unwind =>
        rcases head with ⟨callee,empty⟩
        simp only [PV_STX2_Native.step,waiting,remaining] at eq
        split at eq
        · cases eq
        · cases eq
          refine ⟨tail,?_⟩
          intro wait h
          cases h
          exact ⟨⟨fn,_,_,rfl,callee⟩,empty⟩
      | ret site place =>
        simp only [PV_STX2_Native.step,waiting,remaining] at eq
        split at eq <;> cases eq
      | copy site source destination count => exact False.elim head
      | branch site condition yes no => exact False.elim head
      | switch site condition arms otherwise => exact False.elim head
      | drop site place callee conditional unwind => exact False.elim head
      | unwind site => exact False.elim head
      | abort site kind => exact False.elim head

#print axioms reply
#print axioms step
end PV_FN_THREAD_f6RequestStep
