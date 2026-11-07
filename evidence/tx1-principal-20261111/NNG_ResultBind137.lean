import NNG_SourceStep136
import RSL_Verifier
set_option autoImplicit false
namespace AspisR1.NNG_ResultBind137
open NMT_CallTree NNG_Observed136

theorem sound {A B C D E : Type}
    (code : Code A) (k : A → Code B) (headDecode : A → Except E C)
    (outDecode : B → Except E D) (events : NMT_CallTree.Event → List RSL.Event)
    (env : RSL.Env) (head : RSL.RE E C) (tail : C → RSL.RE E D)
    (headLaw : head env (observation headDecode events code))
    (tailLaw : ∀ a, (observation id events code).exit = .ret a →
      (match headDecode a with
      | .ok c => tail c
      | .error e => RSL.Spec.pure (.error e)) env
        (observation outDecode events (k a))) :
    RSL.RE.bind head tail env
      (observation outDecode events (NMT_CallTree.bind code k)) := by
  rw [NNG_ObservationAlgebra.observation_bind]
  rw [←NNG_InterpretProjection.map_observation headDecode events code] at headLaw
  generalize he : observation id events code = before at headLaw ⊢
  rcases before with ⟨x,ev⟩
  cases x with
  | ret a =>
    have hr : (observation id events code).exit = .ret a := by rw [he]
    refine Or.inl ⟨headDecode a,ev,observation outDecode events (k a),headLaw,?_,rfl⟩
    have ht := tailLaw a hr
    cases hd : headDecode a <;> simpa only [hd] using ht
  | abort => exact Or.inr (Or.inl ⟨ev,headLaw,rfl⟩)
  | diverge => exact Or.inr (Or.inr ⟨ev,headLaw,rfl⟩)
#print axioms sound
end AspisR1.NNG_ResultBind137
