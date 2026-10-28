import R1Z.PV_W_Syntax
set_option autoImplicit false
namespace R1Z.PV_W_SyntaxMap
open PV_W_Syntax PV_W_Threading
universe u v
variable {Op : Type → Type u} {Next : Type → Type v} {E A B W C : Type}

def mapOps (f : {T : Type} → Op T → Next T) : Program Op E A → Program Next E A
  | .pure a => .pure a
  | .failure e => .failure e
  | .diverge => .diverge
  | .call op k => .call (f op) (fun a => mapOps f (k a))

theorem map_bind (f : {T : Type} → Op T → Next T)
    (p : Program Op E A) (k : A → Program Op E B) :
    mapOps f (thenDo p k) = thenDo (mapOps f p) (fun a => mapOps f (k a)) := by
  induction p with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op next ih =>
    change Program.call (f op) (fun a => mapOps f (thenDo (next a) k)) =
      Program.call (f op) (fun a => thenDo (mapOps f (next a)) (fun a => mapOps f (k a)))
    exact congrArg (Program.call (f op)) (funext ih)

/-- Changing only the typed operation representation preserves the entire
state/error/trace result, with the interpreter composed with that same map. -/
theorem eval_map (f : {T : Type} → Op T → Next T)
    (ops : Interpreter Next W C E) (p : Program Op E A) :
    eval ops (mapOps f p) = eval (fun op => ops (f op)) p := by
  induction p with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op next ih =>
    change PV_W_Threading.bind (ops (f op)) (fun a => eval ops (mapOps f (next a))) =
      PV_W_Threading.bind (ops (f op)) (fun a => eval (fun op => ops (f op)) (next a))
    exact congrArg (PV_W_Threading.bind (ops (f op))) (funext ih)

#print axioms map_bind
#print axioms eval_map
end R1Z.PV_W_SyntaxMap
