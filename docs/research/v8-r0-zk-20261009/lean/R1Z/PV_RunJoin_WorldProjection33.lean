import R1Z.PV_W_Syntax
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WorldProjection33
open PV_W_Threading PV_W_Syntax
universe u
variable {Op : Type → Type u} {W V C D E A B : Type}

/-- Transport the entire error/trace/world run. Calls retain their individual
pre-worlds; failed and nonreturning prefixes are not discarded. -/
def project (world : W → V) (tag : C → D) (r : Run W C E A) : Run V D E A :=
  ⟨r.outcome,world r.world,r.calls.map (fun c => (world c.1,tag c.2))⟩

theorem project_lift (world : W → V) (tag : C → D) (r : Outcome E A) (w : W) :
    project world tag (lift r w) = lift r (world w) := rfl

theorem project_bind (world : W → V) (tag : C → D)
    (left : M W C E A) (right : M V D E A)
    (next : A → M W C E B) (target : A → M V D E B)
    (head : ∀ w, project world tag (left w) = right (world w))
    (tail : ∀ a w, project world tag (next a w) = target a (world w)) (w : W) :
    project world tag (bind left next w) = bind right target (world w) := by
  unfold PV_W_Threading.bind
  rw [← head w]
  cases h : (left w).outcome with
  | fail e => simp only [project,h]
  | div => simp only [project,h]
  | ok a =>
    simp only [project,h]
    rw [← tail a (left w).world]
    simp only [project,List.map_append]

/-- A local complete-run law composes on pv-world's existing syntax. This
requires the local source/security-model laws, not just matching values. -/
theorem eval_project (world : W → V) (tag : C → D)
    (left : Interpreter Op W C E) (right : Interpreter Op V D E)
    (local_law : ∀ {B : Type} (op : Op B) w,
      project world tag (left op w) = right op (world w))
    (p : Program Op E A) (w : W) :
    project world tag (eval left p w) = eval right p (world w) := by
  induction p generalizing w with
  | pure a => rfl
  | failure e => rfl
  | diverge => rfl
  | call op next ih =>
    exact project_bind world tag (left op) (right op)
      (fun a => eval left (next a)) (fun a => eval right (next a))
      (local_law op) ih w

#print axioms project_lift
#print axioms project_bind
#print axioms eval_project
end R1Z.PV_RunJoin_WorldProjection33
