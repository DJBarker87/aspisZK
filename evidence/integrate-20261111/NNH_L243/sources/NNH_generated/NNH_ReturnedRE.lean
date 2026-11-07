import NND_ReturnedDomain
import RSL_Verifier
set_option autoImplicit false
namespace NNH_ReturnedRE
open RSL NND_Returned

def bindValue {E A B : Type} (x : Except E A) (k : A → Except E B) : Except E B :=
 match x with | .ok a => k a | .error e => .error e

theorem bind {E A B : Type} (m : RE E A) (k : A → RE E B) (env : Env)
 (x : Except E A) (y : A → Except E B)
 (hm : Returns m env x) (hk : ∀ a, Returns (k a) env (y a)) :
 Returns (RE.bind m k) env (bindValue x y) := by
 unfold RE.bind
 apply NND_Returned.bind _ _ env x _ hm
 cases x with
 | error e => exact NND_Returned.pure env _
 | ok a => exact hk a

theorem pure {E A : Type} (env : Env) (a : A) :
 Returns (RE.pure (ε := E) a) env (.ok a) := NND_Returned.pure env _

theorem lift {E A : Type} (m : Spec A) (env : Env) (a : A) (hm : Returns m env a) :
 Returns (RE.lift (ε := E) m) env (.ok a) := NND_Returned.map _ Except.ok env a hm

theorem ofExcept {E A : Type} (env : Env) (x : Except E A) :
 Returns (RE.ofExcept x) env x := NND_Returned.pure env _

theorem check {E : Type} (env : Env) (b : Bool) (e : E) :
 Returns (RE.check b e) env (if b then .error e else .ok ()) := by
 cases b <;> exact NND_Returned.pure env _

theorem mapErr {E F A : Type} (f : E → F) (m : RE E A) (env : Env)
 (x : Except E A) (hm : Returns m env x) :
 Returns (RE.mapErr f m) env (RE.mapE f x) := by
 unfold RE.mapErr
 exact NND_Returned.map m (RE.mapE f) env x hm

theorem child {E A B : Type} (c : Child A (Except E B)) (a : A) (env : Env)
 (x : Except E B) (h : Returns (c.law a) env x) :
 Returns (c.run a) env x := NND_Returned.call_domain c.dom c.law a env x (fun _ => h)

#print axioms bind
#print axioms pure
#print axioms lift
#print axioms ofExcept
#print axioms check
#print axioms mapErr
#print axioms child
end NNH_ReturnedRE
