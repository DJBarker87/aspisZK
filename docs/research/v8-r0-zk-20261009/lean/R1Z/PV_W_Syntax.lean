import R1Z.PV_W_Threading
set_option autoImplicit false
namespace R1Z.PV_W_Syntax
open PV_W_Threading

/-- Reification retains control flow before a Result evaluator erases calls.
The operation family retains each call's actual argument and return type. -/
inductive Program (Op : Type → Type) (E A : Type) : Type 1 where
  | pure (a : A)
  | failure (e : E)
  | diverge
  | call {B : Type} (op : Op B) (next : B → Program Op E A)

variable {Op : Type → Type} {W C E A B : Type}
abbrev Interpreter (Op : Type → Type) (W C E : Type) :=
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
inductive Executes (ops : Interpreter Op W C E) :
    Program Op E A → W → Run W C E A → Prop where
  | pure (a : A) (w : W) : Executes ops (.pure a) w ⟨.ok a,w,[]⟩
  | failure (e : E) (w : W) : Executes ops (.failure e) w ⟨.fail e,w,[]⟩
  | diverge (w : W) : Executes ops .diverge w ⟨.div,w,[]⟩
  | call_ok {B : Type} (op : Op B) (k : B → Program Op E A)
      (w : W) (a : B) (r : Run W C E A)
      (returns : (ops op w).outcome = .ok a)
      (rest : Executes ops (k a) (ops op w).world r) :
      Executes ops (.call op k) w ⟨r.outcome,r.world,(ops op w).calls ++ r.calls⟩
  | call_fail {B : Type} (op : Op B) (k : B → Program Op E A)
      (w : W) (e : E) (returns : (ops op w).outcome = .fail e) :
      Executes ops (.call op k) w ⟨.fail e,(ops op w).world,(ops op w).calls⟩
  | call_div {B : Type} (op : Op B) (k : B → Program Op E A)
      (w : W) (returns : (ops op w).outcome = .div) :
      Executes ops (.call op k) w ⟨.div,(ops op w).world,(ops op w).calls⟩

theorem execution_sound (ops : Interpreter Op W C E)
    {p : Program Op E A} {w : W} {r : Run W C E A}
    (h : Executes ops p w r) : eval ops p w = r := by
  induction h with
  | pure => rfl
  | failure => rfl
  | diverge => rfl
  | call_ok op k w a r returns rest ih =>
    change bind (ops op) (fun a => eval ops (k a)) w = _
    rw [bind_ok _ _ _ _ returns,ih]
  | call_fail op k w e returns => exact bind_fail _ _ _ _ returns
  | call_div op k w returns => exact bind_div _ _ _ returns

theorem execution_complete (ops : Interpreter Op W C E)
    (p : Program Op E A) (w : W) : Executes ops p w (eval ops p w) := by
  induction p generalizing w with
  | pure a => exact .pure a w
  | failure e => exact .failure e w
  | diverge => exact .diverge w
  | call op k ih =>
    cases h : (ops op w).outcome with
    | ok a =>
      change Executes ops (.call op k) w (bind (ops op) (fun a => eval ops (k a)) w)
      rw [bind_ok _ _ _ _ h]
      exact .call_ok op k w a _ h (ih a _)
    | fail e =>
      change Executes ops (.call op k) w (bind (ops op) (fun a => eval ops (k a)) w)
      rw [bind_fail _ _ _ _ h]
      exact .call_fail op k w e h
    | div =>
      change Executes ops (.call op k) w (bind (ops op) (fun a => eval ops (k a)) w)
      rw [bind_div _ _ _ h]
      exact .call_div op k w h

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
