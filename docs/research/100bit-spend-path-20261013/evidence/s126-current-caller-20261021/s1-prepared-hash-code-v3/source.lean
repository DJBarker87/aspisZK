import S1PreparedHashEffectsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result

/-- Complete typed source hash calls; Result steps retain their own error and
divergence outcomes. No hash input is replaced by a summary identifier. -/
inductive Code (A : Type) : Type 1 where
  | done : A → Code A
  | step {B : Type} : Result B → (B → Code A) → Code A
  | digest {H : Type} (D : aspis_core.Digest32 H) (hash : H)
      (parts : Slice (Slice U8)) : (Array U8 32#usize → Code A) → Code A

def bind {A B : Type} : Code A → (A → Code B) → Code B
  | .done a,k => k a
  | .step r c,k => .step r (fun b => bind (c b) k)
  | .digest D hash parts c,k => .digest D hash parts (fun b => bind (c b) k)

instance : Monad Code where
  pure := Code.done
  bind := bind

instance : MonadLift Result Code where
  monadLift r := .step r .done

def effects : PreparedHashEffects.Effects Code where
  digest := fun D hash parts => .digest D hash parts .done

def erase {A : Type} : Code A → Result A
  | .done a => ok a
  | .step r k => do let value ← r;erase (k value)
  | .digest D hash parts k => do let value ← D.digest hash parts;erase (k value)

/-- Unlike a success-only writer, the log survives a failing/diverging hash
reply. The event records the attempted call and its complete Result reply. -/
inductive Event : Type 1 where
  | digest {H : Type} (D : aspis_core.Digest32 H) (hash : H)
      (parts : Slice (Slice U8)) (reply : Result (Array U8 32#usize))

abbrev Log := List Event

def run {A : Type} : Code A → Log × Result A
  | .done a => ([],ok a)
  | .step r k => match r with
    | .ok value => run (k value)
    | .fail error => ([],.fail error)
    | .div => ([],.div)
  | .digest D hash parts k =>
    match D.digest hash parts with
    | .ok value =>
      let (log,result) := run (k value)
      (Event.digest D hash parts (ok value)::log,result)
    | .fail error => ([Event.digest D hash parts (.fail error)],.fail error)
    | .div => ([Event.digest D hash parts .div],.div)

theorem erase_pure {A : Type} (a : A) : erase (pure a)=ok a := rfl

theorem erase_lift {A : Type} (r : Result A) : erase (monadLift r : Code A)=r := by
  cases r <;> rfl

theorem erase_digest {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (parts : Slice (Slice U8)) : erase (effects.digest D hash parts)=D.digest hash parts := by
  change (do let value ← D.digest hash parts;ok value)=D.digest hash parts
  cases D.digest hash parts <;> rfl

theorem erase_bind {A B : Type} (p : Code A) (k : A → Code B) :
    erase (p >>= k)=(do let value ← erase p;erase (k value)) := by
  induction p with
  | done a => rfl
  | step r next ih =>
    cases r with
    | ok value => exact ih value
    | fail error => rfl
    | div => rfl
  | digest D hash parts next ih =>
    change (do let value ← D.digest hash parts;erase (bind (next value) k)) = _
    have local : ∀ value,erase (bind (next value) k)=
        (do let out ← erase (next value);erase (k out)) := ih
    simp only [local,erase]
    cases D.digest hash parts <;> rfl

theorem run_value {A : Type} (p : Code A) : (run p).2=erase p := by
  induction p with
  | done a => rfl
  | step r next ih =>
    cases r with
    | ok value => exact ih value
    | fail error => rfl
    | div => rfl
  | digest D hash parts next ih =>
    cases reply : D.digest hash parts with
    | ok value => simpa only [run,erase,reply,bind_tc_ok] using ih value
    | fail error => simp only [run,erase,reply,bind_tc_fail]
    | div => simp only [run,erase,reply,bind_tc_div]

#print axioms erase_lift
#print axioms erase_digest
#print axioms erase_bind
#print axioms run_value
end AspisR1PublicPreparation.PreparedHashCode
