import CheckpointBytes5Effect
set_option autoImplicit false
namespace AspisR1.T2Nat_Silent
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes5Effect

/-- A source computation whose syntax has no digest call. Primitive arithmetic
and library calls retain their complete Result, including fail/div. -/
inductive Silent (A : Type) : Type 1 where
  | done : A → Silent A
  | step {B : Type} : Result B → (B → Silent A) → Silent A

def bind {A B : Type} : Silent A → (A → Silent B) → Silent B
  | .done a, k => k a
  | .step r c, k => .step r (fun b => bind (c b) k)
instance : Monad Silent where
  pure := Silent.done
  bind := bind

def call {A : Type} (r : Result A) : Silent A := .step r .done

def erase {A : Type} : Silent A → Result A
  | .done a => ok a
  | .step r k => do let b ← r; erase (k b)

def code {A : Type} : Silent A → Code A
  | .done a => .done a
  | .step r k => .step r (fun b => code (k b))

theorem erase_bind {A B : Type} (c : Silent A) (k : A → Silent B) :
    erase (c >>= k) = (do let a ← erase c; erase (k a)) := by
  induction c with
  | done a => rfl
  | step r c ih =>
    change (do let b ← r; erase (bind (c b) k)) = _
    have h : ∀ b, erase (bind (c b) k) =
      (do let a ← erase (c b); erase (k a)) := ih
    simp only [h,erase]
    cases r <;> rfl

theorem erase_call {A : Type} (r : Result A) : erase (call r) = r := by
  cases r <;> rfl

theorem erase_pure {A : Type} (a : A) : erase (pure a) = ok a := rfl

theorem code_erase {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (c : Silent A) : CheckpointBytes5Effect.erase D hash (code c) = erase c := by
  induction c with
  | done a => rfl
  | step r c ih =>
    change (do let b ← r; CheckpointBytes5Effect.erase D hash (code (c b))) = _
    simp only [ih,erase]

theorem ordered_log {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (c : Silent A) (before : Log) :
    run D hash (code c) before = (do let a ← erase c; ok (a,before)) := by
  induction c with
  | done a => rfl
  | step r c ih =>
    change (do let b ← r; run D hash (code (c b)) before) = _
    simp only [ih,erase]
    cases r <;> rfl

#print axioms erase_bind
#print axioms erase_call
#print axioms erase_pure
#print axioms code_erase
#print axioms ordered_log
end AspisR1.T2Nat_Silent
