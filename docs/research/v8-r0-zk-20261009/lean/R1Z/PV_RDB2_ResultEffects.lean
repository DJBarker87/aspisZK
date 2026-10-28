import Aeneas.Std

/-! Effect summaries retain the recorded world on failures as well as success.
For divergence, this is supplied trace-prefix evidence, not a claim that the
machine terminated with a final heap. -/
namespace R1Z.PV_RDB2_ResultEffects
set_option autoImplicit false
open Aeneas Aeneas.Std Result

abbrev Step (World Value : Type) := World → Result Value × World

def pureStep {World Value : Type} (value : Value) : Step World Value := fun world => (ok value,world)

def bind {World A B : Type} (first : Step World A) (next : A → Step World B) : Step World B :=
  fun world =>
    let (result,after) := first world
    match result with
    | .ok value => next value after
    | .fail error => (.fail error,after)
    | .div => (.div,after)

theorem failure_frame {World A B : Type} (first : Step World A) (next : A → Step World B)
    (world after : World) (error : Error) (h : first world = (.fail error,after)) :
    bind first next world = (.fail error,after) := by simp only [bind,h]

theorem divergence_prefix {World A B : Type} (first : Step World A) (next : A → Step World B)
    (world after : World) (h : first world = (.div,after)) :
    bind first next world = (.div,after) := by simp only [bind,h]

theorem left_identity {World A B : Type} (value : A) (next : A → Step World B) :
    bind (pureStep value) next = next value := rfl

theorem congruence {World A B : Type} (old new : Step World A)
    (left right : A → Step World B) (first : old = new) (rest : ∀ a, left a = right a) :
    bind old left = bind new right := by
  subst new
  have h : left = right := funext rest
  subst right
  rfl

#print axioms failure_frame
#print axioms divergence_prefix
#print axioms left_identity
#print axioms congruence
end R1Z.PV_RDB2_ResultEffects
