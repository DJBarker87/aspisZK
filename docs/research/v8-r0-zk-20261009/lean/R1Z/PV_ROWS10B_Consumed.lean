import Aeneas
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Card
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_Consumed
open Aeneas Aeneas.Std
/-- The op129 carrier, with the dictionary's abstract Error as a parameter.
No conversion to Except or to a success-only carrier is made. -/
abbrev Op (E : Type) := Slice U8 → Result ((core.result.Result Unit E) × Slice U8)
/-- fill_uninit's nonempty branch and fill's unit/error propagation. The
backend already returns the restored complete mutable slice on inner Err. -/
def fill {E : Type} (backend : Op E) (s : Slice U8) :
    Result ((core.result.Result Unit E) × Slice U8) :=
  if s.val.length = 0 then .ok (.Ok (), s) else
  match backend s with
  | .ok (.Ok _, after) => .ok (.Ok (), after)
  | .ok (.Err e, after) => .ok (.Err e, after)
  | .fail e => .fail e
  | .div => .div
/-- Divergence and outer failure are distinguished from the option-B OS error. -/
inductive Stop where
  | returned (osError : Bool)
  | aborted (error : Aeneas.Std.Error)
  | diverged

def stop {E : Type} : Result ((core.result.Result Unit E) × Slice U8) → Stop
  | .ok (.Ok _, _) => .returned false
  | .ok (.Err _, _) => .returned true
  | .fail e => .aborted e
  | .div => .diverged

def requestStop (control : Nat → Stop) (n : Nat) : Stop :=
  if n = 0 then .returned false else control n

variable {E W C Word Raw : Type}
/-- Native selection/source association; must be discharged against the
selected source. This is not an installed dictionary update. -/
def PV_ROWS10B_Link_Entry (native source : W → Op E) : Prop := native = source
/-- Complete source body binding, including all backend error/abort/divergence
branches. This is the own-1 obligation, not an entropy premise. -/
def PV_ROWS10B_Link_Body (source backend : W → Op E) : Prop :=
  ∀ w s, source w s = fill (backend w) s
/-- The public interpreter discards byte values only; exact results remain
in Link_Body. -/
def PV_ROWS10B_Link_Control (backend : W → Op E) (word : W → C → Word)
    (interpret : Word → Nat → Stop) : Prop :=
  ∀ w c s, stop (backend w s) = interpret (word w c) s.val.length
/-- The actual caller's environmental control must be coupled across private
witnesses at each shared public context. It does not follow from E1. -/
def PV_ROWS10B_Link_Public (word : W → C → Word) : Prop :=
  ∀ a b c, word a c = word b c
/-- Association of the consumed callback density with the *retained* T law.
This is a source/callback coordinate obligation, not a new trust field. -/
def PV_ROWS10B_Link_Callback (callback law : C → Raw → ℚ) : Prop := callback = law

theorem fill_stop (backend : Op E) (s : Slice U8) :
    stop (fill backend s) = requestStop (fun _ => stop (backend s)) s.val.length := by
  unfold fill requestStop
  split
  · rfl
  · cases backend s with
    | ok pair => rcases pair with ⟨r, after⟩; cases r <;> rfl
    | fail e => rfl
    | div => rfl

/-- Top-down consumed law. Each link concerns a distinct boundary. The result
keeps the entire op129 Result and the callback's exact E1 schema. -/
theorem consumed [Fintype Raw]
    (native source backend : W → Op E) (word : W → C → Word)
    (interpret : Word → Nat → Stop) (callback law : C → Raw → ℚ)
    (entry : PV_ROWS10B_Link_Entry native source)
    (body : PV_ROWS10B_Link_Body source backend)
    (control : PV_ROWS10B_Link_Control backend word interpret)
    (public : PV_ROWS10B_Link_Public word)
    (coordinates : PV_ROWS10B_Link_Callback callback law)
    (entropy_law : ∀ c raw, law c raw = 1 / (Fintype.card Raw : ℚ)) :
    (∀ w s, native w s = fill (backend w) s) ∧
    (∀ a b c (sa sb : Slice U8), sa.val.length = sb.val.length →
      stop (native a sa) = stop (native b sb)) ∧
    (∀ c raw, callback c raw = 1 / (Fintype.card Raw : ℚ)) := by
  have full : ∀ w s, native w s = fill (backend w) s := by
    rw [entry]; exact body
  refine ⟨full, ?_, ?_⟩
  · intro a b c sa sb len
    rw [full, full, fill_stop, fill_stop]
    unfold requestStop
    rw [len, control a c sa, control b c sb, public a b c, len]
  · rw [coordinates]; exact entropy_law
#print axioms fill_stop
#print axioms consumed
end R1Z.PV_ROWS10B_Consumed
