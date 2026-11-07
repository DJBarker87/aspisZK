import RSL_Base
set_option autoImplicit false
namespace PCM_Returns
open RSL
/-- Returned-value evaluator; abort/divergence prefixes remain in the law. -/
def Returns {A : Type} (m : Spec A) (env : Env) (value : A) : Prop :=
  ∀ o v, m env o → o.exit = .ret v → v = value

theorem pure {A : Type} (env : Env) (value : A) :
    Returns (Spec.pure value) env value := by
  intro o v h he
  subst o
  exact (Exit.ret.inj he).symm
#print axioms pure
end PCM_Returns
