import NMX_SpecAssociativity
set_option autoImplicit false
namespace NMX_RSNormalize
open RSL

theorem bind_if {A B : Type} (b : Bool) (yes no : RS A) (next : A → RS B) :
 RS.bind (if b then yes else no) next = if b then RS.bind yes next else RS.bind no next := by
 cases b <;> rfl

theorem check_bind {A : Type} (b : Bool) (e : ProgramError) (next : Unit → RS A) :
 RS.bind (RS.check b e) next = if b then RS.throw e else next () := by
 cases b <;> simp [RS.check,RS.bind_throw,RS.bind_pure]

theorem condition_or {A : Type} (a b : Bool) (yes no : A) :
 (if a || b then yes else no) = if a then yes else if b then yes else no := by
 cases a <;> cases b <;> rfl
#print axioms bind_if
#print axioms check_bind
#print axioms condition_or
end NMX_RSNormalize
