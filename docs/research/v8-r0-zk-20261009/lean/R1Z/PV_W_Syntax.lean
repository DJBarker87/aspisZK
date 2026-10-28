import R1Z.PV_W_Threading
set_option autoImplicit false
namespace R1Z.PV_W_Syntax
open PV_W_Threading
universe u

/-- Reification retains control flow before a Result evaluator erases calls.
The operation family retains each call's actual argument and return type. -/
inductive Program (Op : Type → Type u) (E A : Type) : Type (max 1 u) where
  | pure (a : A)
  | failure (e : E)
  | diverge
  | call {B : Type} (op : Op B) (next : B → Program Op E A)

variable {Op : Type → Type u} {W C E A B : Type}
abbrev Interpreter (Op : Type → Type u) (W C E : Type) :=
  {B : Type} → Op B → M W C E B

def eval (ops : Interpreter Op W C E) : Program Op E A → M W C E A
  | .pure a => lift (.ok a)
  | .failure e => lift (.fail e)
  | .diverge => lift .div
  | .call op next => bind (ops op) (fun a => eval ops (next a))

def thenDo (p : Program Op E A) (k : A → Program Op E B) : Program Op E B :=
  match p with
  | .pure a => k a
  | .failure e => .failure e
  | .diverge => .diverge
  | .call op next => .call op (fun a => thenDo (next a) k)

theorem eval_thenDo (ops : Interpreter Op W C E)
    (p : Program Op E A) (k : A → Program Op E B) :
    eval ops (thenDo p k) = bind (eval ops p) (fun a => eval ops (k a)) := by
  induction p with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op next ih =>
    simp only [thenDo,eval]
    rw [bind_assoc]
    congr 1
    funext a
    exact ih a

/-- Independent big-step execution judgment: each successful call hands its
post-state to the selected continuation; failed/nonreturning calls stop it. -/
def Executes (ops : Interpreter Op W C E) :
    Program Op E A → W → Run W C E A → Prop
  | .pure a, w, r => r = ⟨.ok a,w,[]⟩
  | .failure e, w, r => r = ⟨.fail e,w,[]⟩
  | .diverge, w, r => r = ⟨.div,w,[]⟩
  | .call op k, w, r =>
    match (ops op w).outcome with
    | .ok a => ∃ tail : Run W C E A,
        Executes ops (k a) (ops op w).world tail ∧
        r = ⟨tail.outcome,tail.world,(ops op w).calls ++ tail.calls⟩
    | .fail e => r = ⟨.fail e,(ops op w).world,(ops op w).calls⟩
    | .div => r = ⟨.div,(ops op w).world,(ops op w).calls⟩

theorem execution_sound (ops : Interpreter Op W C E)
    {p : Program Op E A} {w : W} {r : Run W C E A}
    (h : Executes ops p w r) : eval ops p w = r := by
  induction p generalizing w r with
  | pure a => exact h.symm
  | failure e => exact h.symm
  | diverge => exact h.symm
  | call op k ih =>
    cases returns : (ops op w).outcome with
    | ok a =>
      obtain ⟨tail,rest,eq⟩ := (show ∃ tail : Run W C E A,
        Executes ops (k a) (ops op w).world tail ∧
        r = ⟨tail.outcome,tail.world,(ops op w).calls ++ tail.calls⟩ by
          simpa only [Executes,returns] using h)
      change bind (ops op) (fun a => eval ops (k a)) w = _
      rw [bind_ok _ _ _ _ returns,ih a rest]
      exact eq.symm
    | fail e =>
      change bind (ops op) (fun a => eval ops (k a)) w = _
      rw [bind_fail _ _ _ _ returns]
      exact (show r = _ by simpa only [Executes,returns] using h).symm
    | div =>
      change bind (ops op) (fun a => eval ops (k a)) w = _
      rw [bind_div _ _ _ returns]
      exact (show r = _ by simpa only [Executes,returns] using h).symm

theorem execution_complete (ops : Interpreter Op W C E)
    (p : Program Op E A) (w : W) : Executes ops p w (eval ops p w) := by
  induction p generalizing w with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op k ih =>
    cases h : (ops op w).outcome with
    | ok a =>
      simp only [Executes,h]
      exact ⟨eval ops (k a) (ops op w).world,ih a _,bind_ok _ _ _ _ h⟩
    | fail e => simp only [Executes,eval,PV_W_Threading.bind,h]
    | div => simp only [Executes,eval,PV_W_Threading.bind,h]

theorem eval_valid (ops : Interpreter Op W C E) (step : W → C → W → Prop)
    (leaves : ∀ {B : Type} (op : Op B), Valid step (ops op))
    (p : Program Op E A) : Valid step (eval ops p) := by
  induction p with
  | pure a => exact valid_lift step _
  | failure e => exact valid_lift step _
  | diverge => exact valid_lift step _
  | call op k ih => exact valid_bind step _ _ (leaves op) ih

/-- Exact outcome, post-world and ordered pre-world tags of an operational
execution, proved by control-flow composition, not concrete run reduction. -/
theorem execution_exact (ops : Interpreter Op W C E) (step : W → C → W → Prop)
    (leaves : ∀ {B : Type} (op : Op B), Valid step (ops op))
    {p : Program Op E A} {w : W} {r : Run W C E A}
    (h : Executes ops p w r) :
    (eval ops p w).outcome = r.outcome ∧
    (eval ops p w).calls = r.calls ∧
    (eval ops p w).world = r.world ∧ Threaded step w r.calls r.world := by
  have eq := execution_sound ops h
  refine ⟨congrArg Run.outcome eq,congrArg Run.calls eq,congrArg Run.world eq,?_⟩
  rw [← eq]
  exact eval_valid ops step leaves p w

#print axioms eval_thenDo
#print axioms execution_sound
#print axioms execution_complete
#print axioms eval_valid
#print axioms execution_exact
end R1Z.PV_W_Syntax
