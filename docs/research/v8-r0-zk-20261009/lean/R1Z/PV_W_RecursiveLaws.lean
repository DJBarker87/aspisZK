import R1Z.PV_W_TypedEffects
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_RecursiveLaws
open Aeneas.Std ProverRwFull PV_W_TypedEffects PV_W_Syntax PV_W_Threading
variable [ExternalTypes]

theorem erase_ite {A : Type} (ops : ExternalFuns) (p : Prop) [Decidable p]
    (yes no : P A) : erase ops (if p then yes else no) =
      if p then erase ops yes else erase ops no := by
  by_cases h : p <;> simp only [h,↓reduceIte]

theorem bind_congr {A B : Type} (left right : Aeneas.Std.Result A)
    (k l : A → Aeneas.Std.Result B) (h : left = right)
    (next : ∀ a, k a = l a) :
    Aeneas.Std.bind left k = Aeneas.Std.bind right l := by
  rw [h]
  exact PV_W_SourceSyntax.source_bind_congr right k l next

/-- Subprogram replacement preserves all effects, including errors and
nonreturning prefixes. The premise is an equality in the full calculus,
not just equality of returned values. -/
def expand {Op : Type → Type 1} {A : Type}
    (replace : {B : Type} → Op B → Program Op Aeneas.Std.Error B) :
    Program Op Aeneas.Std.Error A → Program Op Aeneas.Std.Error A
  | .pure a => .pure a
  | .failure e => .failure e
  | .diverge => .diverge
  | .call op k => thenDo (replace op) (fun a => expand replace (k a))

theorem eval_expand {Op : Type → Type 1} {W C A : Type}
    (ops : Interpreter Op W C Aeneas.Std.Error)
    (replace : {B : Type} → Op B → Program Op Aeneas.Std.Error B)
    (localLaw : ∀ {B : Type} (op : Op B), eval ops (replace op) = ops op)
    (p : Program Op Aeneas.Std.Error A) : eval ops (expand replace p) = eval ops p := by
  induction p with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op k ih =>
    rw [expand,eval_thenDo,localLaw]
    change PV_W_Threading.bind (ops op) (fun a => eval ops (expand replace (k a))) = _
    exact congrArg (PV_W_Threading.bind (ops op)) (funext ih)

#print axioms erase_ite
#print axioms bind_congr
#print axioms eval_expand
end R1Z.PV_W_RecursiveLaws
