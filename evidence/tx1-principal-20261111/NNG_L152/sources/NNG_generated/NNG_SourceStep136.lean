import NNG_InterpretProjection
set_option autoImplicit false
namespace AspisR1.NNG_SourceStep136
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_ObservationAlgebra NNG_InterpretProjection

def Within {A B : Type} (suffix : Code A) (whole : Code B) : Prop :=
  ∀ e, e ∈ (run suffix).2 → e ∈ (run whole).2

theorem within_refl {A : Type} (code : Code A) : Within code code := fun _ h => h
#print axioms within_refl

theorem within_trans {A B C : Type} (a : Code A) (b : Code B) (c : Code C)
    (hab : Within a b) (hbc : Within b c) : Within a c := fun e h => hbc e (hab e h)
#print axioms within_trans

/-- A child trace is always a prefix of the same parent's trace, including
outer abort/divergence; no different invocation is selected. -/
theorem within_head {A B : Type} (code : Code A) (k : A → Code B) :
    Within code (NMT_CallTree.bind code k) := by
  intro e he
  rw [run_bind]
  generalize h : run code = out at he ⊢
  rcases out with ⟨r,log⟩
  cases r with
  | ok a => exact List.mem_append_left _ he
  | fail err => exact he
  | div => exact he
#print axioms within_head

theorem returned_run {A : Type} (events : NMT_CallTree.Event → List RSL.Event)
    (code : Code A) (a : A)
    (returned : (observation id events code).exit = .ret a) : (run code).1 = .ok a := by
  unfold observation at returned
  generalize (run code).1 = r at returned ⊢
  cases r with
  | ok value => exact congrArg Result.ok (RSL.Exit.ret.inj returned)
  | fail err => cases returned
  | div => cases returned
#print axioms returned_run

/-- Only an actual returned head exposes a suffix. Its calls belong to the
SAME whole trace and may consume the per-occurrence CLOSED laws there. -/
theorem within_tail {A B : Type} (code : Code A) (k : A → Code B) (a : A)
    (returned : (run code).1 = .ok a) : Within (k a) (NMT_CallTree.bind code k) := by
  intro e he
  rw [run_bind, returned]
  exact List.mem_append_right _ he
#print axioms within_tail

/-- One forward source step, projecting only the values that this SAME head
actually returns. The continuation is never demanded after a stop. -/
theorem bind_sound {A B C D : Type}
    (code : Code A) (k : A → Code B) (headDecode : A → C) (outDecode : B → D)
    (events : NMT_CallTree.Event → List RSL.Event) (env : RSL.Env)
    (head : RSL.Spec C) (tail : C → RSL.Spec D)
    (headLaw : head env (observation headDecode events code))
    (tailLaw : ∀ a, (observation id events code).exit = .ret a →
      tail (headDecode a) env (observation outDecode events (k a))) :
    RSL.Spec.bind head tail env
      (observation outDecode events (NMT_CallTree.bind code k)) := by
  rw [observation_bind]
  rw [←map_observation headDecode events code] at headLaw
  generalize he : observation id events code = before at headLaw ⊢
  rcases before with ⟨x,ev⟩
  cases x with
  | ret a =>
    have hr : (observation id events code).exit = .ret a := by rw [he]
    exact Or.inl ⟨headDecode a,ev,observation outDecode events (k a),headLaw,tailLaw a hr,rfl⟩
  | abort => exact Or.inr (Or.inl ⟨ev,headLaw,rfl⟩)
  | diverge => exact Or.inr (Or.inr ⟨ev,headLaw,rfl⟩)
#print axioms bind_sound
end AspisR1.NNG_SourceStep136
