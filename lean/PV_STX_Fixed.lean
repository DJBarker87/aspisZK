import PV_STX_Machine
set_option autoImplicit false
noncomputable section
namespace PV_STX_Fixed
open Aeneas Aeneas.Std PV_STX_Code PV_STX_Machine
variable {Op : Type → Type 1} {W E A : Type}

def handler (fixed : {X : Type} → Op X → Result X) : Handler Op W E :=
  fun op w => ⟨.returned (fixed op),w,[]⟩

def view (fixed : {X : Type} → Op X → Result X) : Status Op A → Option (Result A)
  | .running c => some (configDenote fixed c)
  | .returned r => some r
  | .fault _ => none

theorem kont_fail (fixed : {X : Type} → Op X → Result X)
    {X : Type} (k : Kont Op A X) (e : Error) :
    kontDenote fixed k (.fail e) = .fail e := by
  induction k with
  | done => rfl
  | seq next rest ih => exact ih
  | loop body rest ih => exact ih

theorem kont_div (fixed : {X : Type} → Op X → Result X)
    {X : Type} (k : Kont Op A X) : kontDenote fixed k .div = .div := by
  induction k with
  | done => rfl
  | seq next rest ih => exact ih
  | loop body rest ih => exact ih

theorem resumed_view (fixed : {X : Type} → Op X → Result X)
    {X : Type} (k : Kont Op A X) (x : X) :
    view fixed (resumed (@continueWith Op A) k x) = some (kontDenote fixed k (.ok x)) := by
  cases k with
  | done => rfl
  | seq next rest => rfl
  | loop body rest => cases x <;> rfl

theorem step_view (fixed : {X : Type} → Op X → Result X)
    (c : Config Op A) (w : W) :
    view fixed (step (handler (E := E) fixed) c w).status = some (configDenote fixed c) := by
  rcases c with ⟨X,code,k⟩
  cases code with
  | result r =>
    cases r with
    | ok a => exact resumed_view fixed k a
    | fail e => exact congrArg some (kont_fail fixed k e).symm
    | div => exact congrArg some (kont_div fixed k).symm
  | seq first next => rfl
  | loop body s =>
    simp only [step,view,configDenote,kontDenote,denote]
    conv => rhs; rw [Aeneas.Std.loop.eq_def]
  | call op =>
    cases h : fixed op with
    | ok a => simpa only [step,handler,h,configDenote,denote] using resumed_view fixed k a
    | fail e => simpa only [step,handler,h,configDenote,denote,view] using
        congrArg some (kont_fail fixed k e).symm
    | div => simpa only [step,handler,h,configDenote,denote,view] using
        congrArg some (kont_div fixed k).symm

theorem advance_view (fixed : {X : Type} → Op X → Result X)
    (n : Nat) (p : Prefix Op W E A) :
    view fixed (advance (handler fixed) n p).status = view fixed p.status := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    cases hp : p.status with
    | returned r => simp only [advance,hp]
    | fault f => simp only [advance,hp]
    | running c =>
      rw [advance,hp,ih]
      exact step_view fixed c p.world

/-- No compatibility premise or supplied whole-helper run: the fixed handler
is constructed, and the residual source denotation is preserved at EVERY fuel. -/
theorem run_view (fixed : {X : Type} → Op X → Result X)
    (n : Nat) (code : Code Op A) (w : W) :
    view fixed (run (handler (E := E) fixed) n code w).status = some (denote fixed code) :=
  advance_view fixed n ⟨.running (start code),w,[]⟩

theorem returned_agrees (fixed : {X : Type} → Op X → Result X)
    (n : Nat) (code : Code Op A) (w : W) (r : Result A)
    (h : (run (handler (E := E) fixed) n code w).status = .returned r) :
    denote fixed code = r := by
  have hv := run_view (E := E) fixed n code w
  rw [h] at hv
  exact (Option.some.inj hv).symm

#print axioms kont_fail
#print axioms kont_div
#print axioms resumed_view
#print axioms step_view
#print axioms advance_view
#print axioms run_view
#print axioms returned_agrees
end PV_STX_Fixed
