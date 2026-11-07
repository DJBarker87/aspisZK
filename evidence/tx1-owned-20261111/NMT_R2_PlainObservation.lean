import NMT_345Semantic
import NMT_R2_ConcreteS1
set_option autoImplicit false
noncomputable section
namespace NMT_R2_PlainObservation
open Aeneas Aeneas.Std NMT_345 RSL

def observe {A B : Type} (f : A → B) : Result A → Obs B
 | .ok a => ⟨.ret (f a),[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩

theorem semantic (V : VLib) (encodePublic : Public → V.Public) (st : Statement) (env : Env) :
 Spec.pure ((NMT_R2_ConcreteS1.library V encodePublic).semanticPublic st) env
  (observe id (semanticCall st)) := by
 rw [semantic_value]
 rfl

theorem common (st : Statement) (env : Env) :
 Spec.pure (commonValue st) env (observe id (commonCall st)) := rfl
#print axioms semantic
#print axioms common
end NMT_R2_PlainObservation
end
