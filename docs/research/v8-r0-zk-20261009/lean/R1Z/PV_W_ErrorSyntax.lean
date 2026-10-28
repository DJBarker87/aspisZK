import R1Z.PV_W_Syntax
set_option autoImplicit false
namespace R1Z.PV_W_ErrorSyntax
open PV_W_Syntax PV_W_Threading
universe u
variable {Op : Type → Type u} {W C E F A B : Type}

def outcomeError (f : E → F) : Outcome E A → Outcome F A
  | .ok a => .ok a
  | .fail e => .fail (f e)
  | .div => .div

def runError (f : E → F) (r : Run W C E A) : Run W C F A :=
  ⟨outcomeError f r.outcome,r.world,r.calls⟩

def actionError (f : E → F) (m : M W C E A) : M W C F A := fun w => runError f (m w)

def programError (f : E → F) : Program Op E A → Program Op F A
  | .pure a => .pure a
  | .failure e => .failure (f e)
  | .diverge => .diverge
  | .call op k => .call op (fun a => programError f (k a))

theorem error_bind (f : E → F) (m : M W C E A) (k : A → M W C E B) :
    actionError f (PV_W_Threading.bind m k) =
      PV_W_Threading.bind (actionError f m) (fun a => actionError f (k a)) := by
  funext w
  cases h : (m w).outcome <;> simp only [actionError,runError,outcomeError,PV_W_Threading.bind,h]

theorem error_eval (f : E → F) (ops : Interpreter Op W C E) (p : Program Op E A) :
    eval (fun op => actionError f (ops op)) (programError f p) = actionError f (eval ops p) := by
  induction p with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op next ih =>
    change PV_W_Threading.bind (actionError f (ops op))
      (fun a => eval (fun op => actionError f (ops op)) (programError f (next a))) =
      actionError f (PV_W_Threading.bind (ops op) (fun a => eval ops (next a)))
    rw [error_bind]
    exact congrArg (PV_W_Threading.bind (actionError f (ops op))) (funext ih)

/-- Error embeddings preserve both successful and failed observable prefixes. -/
theorem error_frame (f : E → F) (m : M W C E A) (w : W) :
    (actionError f m w).world = (m w).world ∧
    (actionError f m w).calls = (m w).calls := ⟨rfl,rfl⟩

#print axioms error_bind
#print axioms error_eval
#print axioms error_frame
end R1Z.PV_W_ErrorSyntax
