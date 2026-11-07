import RSL_Base
set_option autoImplicit false
namespace NND_Returned
open RSL
/-- Returned-arm value law. Stops remain possible; no event or heap is erased
from the reference observation. This is support for A1/A2, not a RowSpec. -/
def Returns {α : Type} (m : Spec α) (env : Env) (x : α) : Prop :=
 ∀ o r, m env o → o.exit = .ret r → r = x

theorem pure {α : Type} (env : Env) (x : α) : Returns (Spec.pure x) env x := by
 intro o r h hr
 subst h
 exact Exit.ret.inj hr |>.symm

theorem bind {α β : Type} (m : Spec α) (k : α → Spec β) (env : Env)
 (x : α) (y : β) (hm : Returns m env x) (hk : Returns (k x) env y) :
 Returns (Spec.bind m k) env y := by
 intro o r h hr
 rcases h with ⟨a,e1,o2,h1,h2,ho⟩ | ⟨e1,h1,ho⟩ | ⟨e1,h1,ho⟩
 · have ha := hm _ a h1 rfl
   subst a
   subst ho
   exact hk o2 r h2 hr
 · subst ho
   cases hr
 · subst ho
   cases hr

theorem map {α β : Type} (m : Spec α) (f : α → β) (env : Env)
 (x : α) (hm : Returns m env x) : Returns (Spec.map f m) env (f x) :=
 bind m _ env x (f x) hm (pure env (f x))

theorem emit (env : Env) (ev : Event) : Returns (Spec.emit ev) env () := by
 intro o r h hr
 subst h
 exact Exit.ret.inj hr |>.symm

theorem alloc (env : Env) : Returns Spec.alloc env () := by
 intro o r h hr
 rcases h with h | h <;> subst h
 · exact Exit.ret.inj hr |>.symm
 · cases hr

theorem environment {α : Type} (env : Env) (f : Env → α) :
 Returns (Spec.env f) env (f env) := by
 intro o r h hr
 subst h
 exact Exit.ret.inj hr |>.symm

theorem call {A B : Type} (dom : A → Prop) (law : A → Spec B) (a : A)
 (env : Env) (x : B) (h : Returns (law a) env x) :
 Returns (Spec.call dom law a) env x := by
 intro o r hcall hr
 exact h o r hcall.2 hr

theorem panic {α : Type} (env : Env) (x : α) : Returns Spec.panic env x := by
 intro o r h hr
 subst h
 cases hr

theorem rs_pure {α : Type} (env : Env) (x : α) : Returns (RS.pure x) env (.ok x) := pure env _
theorem throw {α : Type} (env : Env) (e : ProgramError) :
 Returns (RS.throw e : RS α) env (.error e) := pure env _
theorem ofExcept {α : Type} (env : Env) (x : Except ProgramError α) :
 Returns (RS.ofExcept x) env x := pure env _

def ebind {α β : Type} (x : Except ProgramError α) (k : α → Except ProgramError β) :
 Except ProgramError β := match x with | .ok a => k a | .error e => .error e

theorem rs_bind {α β : Type} (m : RS α) (k : α → RS β) (env : Env)
 (x : Except ProgramError α) (f : α → Except ProgramError β)
 (hm : Returns m env x) (hk : ∀ a, Returns (k a) env (f a)) :
 Returns (RS.bind m k) env (ebind x f) := by
 unfold RS.bind
 apply bind m _ env x _ hm
 cases x with
 | ok a => exact hk a
 | error e => exact pure env _

theorem rs_lift {α : Type} (m : Spec α) (env : Env) (x : α)
 (hm : Returns m env x) : Returns (RS.lift m) env (.ok x) := map m _ env x hm

theorem check (env : Env) (b : Bool) (e : ProgramError) :
 Returns (RS.check b e) env (if b then .error e else .ok ()) := by
 cases b
 · exact rs_pure env ()
 · exact throw env e

theorem ofOption {α : Type} (env : Env) (x : Option α) (e : ProgramError) :
 Returns (RS.ofOption x e) env ((match x with | some a => .ok a | none => .error e)) := by
 cases x with
 | none => exact throw env e
 | some a => exact rs_pure env a

#print axioms pure
#print axioms bind
#print axioms map
#print axioms emit
#print axioms alloc
#print axioms environment
#print axioms call
#print axioms panic
#print axioms rs_pure
#print axioms throw
#print axioms ofExcept
#print axioms rs_bind
#print axioms rs_lift
#print axioms check
#print axioms ofOption
end NND_Returned
