import Stage2ContinuationResumeBody

/-! A reified effect schedule with an ordered state interpreter. Pure Aeneas
operations retain failures/divergence; inner verifier errors are ordinary
values and retain the log. The state equations follow the D138 state lift.
Reification makes erasure a generic theorem, rather than a source hypothesis. -/
set_option autoImplicit false
namespace AspisR1.CheckpointBytes5Effect
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Parts := Slice (Slice U8)
abbrev Digest := Array U8 32#usize
abbrev Log := List (Parts × Digest)
abbrev Port (S A : Type) := StateT S Result A

inductive Code (A : Type) : Type 1 where
  | done : A → Code A
  | step {B : Type} : Result B → (B → Code A) → Code A
  | read : Parts → (Digest → Code A) → Code A

def bind {A B : Type} : Code A → (A → Code B) → Code B
  | .done a, k => k a
  | .step r c, k => .step r (fun b => bind (c b) k)
  | .read parts c, k => .read parts (fun b => bind (c b) k)
instance : Monad Code where
  pure := Code.done
  bind := bind

def liftResult {A : Type} (r : Result A) : Code A := .step r .done
def read (parts : Parts) : Code Digest := .read parts .done

def erase {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) : Code A → Result A
  | .done a => ok a
  | .step r k => do let b ← r; erase D hash (k b)
  | .read parts k => do let b ← D.digest hash parts; erase D hash (k b)

def run {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) : Code A → Port Log A
  | .done a => fun log => ok (a,log)
  | .step r k => fun log => do let b ← r; run D hash (k b) log
  | .read parts k => fun log => do
      let b ← D.digest hash parts
      run D hash (k b) (log ++ [(parts,b)])

theorem bind_run {S A B : Type} (p : Port S A) (k : A → Port S B) (state : S) :
    (p >>= k) state = (do let (value,next) ← p state; k value next) := rfl

theorem erase_bind {A B H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : Code A) (k : A → Code B) :
    erase D hash (p >>= k) = (do let a ← erase D hash p; erase D hash (k a)) := by
  induction p with
  | done a => rfl
  | step r c ih =>
    change (do let b ← r; erase D hash (bind (c b) k)) = _
    have h : ∀ b, erase D hash (bind (c b) k) =
      (do let a ← erase D hash (c b); erase D hash (k a)) := ih
    simp only [h,erase]
    cases r <;> rfl
  | read parts c ih =>
    change (do let b ← D.digest hash parts; erase D hash (bind (c b) k)) = _
    have h : ∀ b, erase D hash (bind (c b) k) =
      (do let a ← erase D hash (c b); erase D hash (k a)) := ih
    simp only [h,erase]
    cases D.digest hash parts <;> rfl

theorem erase_lift {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) (r : Result A) :
    erase D hash (liftResult r) = r := by cases r <;> rfl

theorem erase_read {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) (p : Parts) :
    erase D hash (read p) = D.digest hash p := by
  simp only [read,erase]
  cases D.digest hash p <;> rfl

theorem erase_pure {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H) (a : A) :
    erase D hash (pure a) = ok a := rfl

theorem run_success {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : Code A) (before after : Log) (a : A)
    (success : run D hash p before = ok (a,after)) : erase D hash p = ok a := by
  induction p generalizing before after with
  | done b => exact congrArg (fun x => ok x.1) (Result.ok.inj success)
  | step r k ih =>
    cases r with
    | fail e => cases success
    | div => cases success
    | ok b => exact ih b before after success
  | read parts k ih =>
    cases call : D.digest hash parts with
    | fail e => simp only [run,call,bind_tc_fail] at success; cases success
    | div => simp only [run,call,bind_tc_div] at success; cases success
    | ok b =>
      simp only [run,call,bind_tc_ok] at success
      simpa only [erase,call,bind_tc_ok] using ih b _ _ success

theorem run_bind {A B H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : Code A) (k : A → Code B) (log : Log) :
    run D hash (p >>= k) log =
      (do let (a,next) ← run D hash p log; run D hash (k a) next) := by
  induction p generalizing log with
  | done a => rfl
  | step r c ih =>
    change (do let b ← r; run D hash (bind (c b) k) log) = _
    have h : ∀ b log, run D hash (bind (c b) k) log =
      (do let (a,next) ← run D hash (c b) log; run D hash (k a) next) := ih
    simp only [h,run]
    cases r <;> rfl
  | read parts c ih =>
    change (do let b ← D.digest hash parts; run D hash (bind (c b) k) (log ++ [(parts,b)])) = _
    have h : ∀ b log, run D hash (bind (c b) k) log =
      (do let (a,next) ← run D hash (c b) log; run D hash (k a) next) := ih
    simp only [h,run]
    cases D.digest hash parts <;> rfl

theorem run_lift {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (r : Result A) (log : Log) :
    run D hash (liftResult r) log = (do let a ← r; ok (a,log)) := rfl

theorem run_read {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (parts : Parts) (log : Log) :
    run D hash (read parts) log =
      (do let b ← D.digest hash parts; ok (b,log ++ [(parts,b)])) := rfl

theorem run_pure {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (a : A) (log : Log) : run D hash (pure a) log = ok (a,log) := rfl

theorem erase_ite {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : Prop) [Decidable p] (yes no : Code A) :
    erase D hash (if p then yes else no) =
      if p then erase D hash yes else erase D hash no := by split <;> rfl

theorem run_ite {A H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : Prop) [Decidable p] (yes no : Code A) (log : Log) :
    run D hash (if p then yes else no) log =
      if p then run D hash yes log else run D hash no log := by split <;> rfl

#print axioms erase_ite
#print axioms run_ite

#print axioms run_bind
#print axioms run_lift
#print axioms run_read
#print axioms run_pure

#print axioms bind_run
#print axioms erase_bind
#print axioms erase_lift
#print axioms erase_read
#print axioms erase_pure
#print axioms run_success
end AspisR1.CheckpointBytes5Effect
