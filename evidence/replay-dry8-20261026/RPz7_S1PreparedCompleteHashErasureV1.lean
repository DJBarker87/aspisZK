import RPz7_S1PreparedQueryErasureV1
import RPz7_S1PreparedSourceEffectsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result ControlFlow

def withQueries (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries) :
    PreparedScratchModel.Boundaries :=
  {B with sampling := {B.sampling with queries := QueriesModel.queries Q}}

/-- Native-shaped hash children, retaining the complete scalar/query source
procedures. The non-hash boundaries remain explicit, rather than being claimed
pure merely because their Result values can be lifted. -/
def preparationEffects (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries) :
    PreparedSourceEffects.Effects Code where
  newTranscript := PreparedHashEffects.new effects
  scalar := PreparedScalarEffects.scalar effects B.sampling
  toBytes := fun x => monadLift (B.sampling.toBytes x)
  queries := PreparedQueryEffects.queries effects Q
  rho := PreparedScalarEffects.scalar_k effects B.sampling
  powers := fun N x => monadLift (B.powers N x)
  claim := fun D sem bytes inactive powers kappa =>
    monadLift (B.claim D sem bytes inactive powers kappa)

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Full preparation Result and returned scratch, for both variants and all
errors/divergence. No success premise or independently assumed child run. -/
theorem preparation_erasure (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (view : verifier.View) (hash : H) (scratch : Array aspis_core.field.WideExact 29#usize) :
    erase (PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash scratch)=
      OriginalPreparedNative.prepare (withQueries B Q) D sem view hash scratch := by
  unfold PreparedSourceEffects.prepare OriginalPreparedNative.prepare
  simp only [preparationEffects,withQueries]
  repeat' first
    | (rw [erase_bind]
       first
       | rw [erase_lift]
       | rw [new_erasure]
       | rw [scalar_erasure]
       | rw [scalar_k_erasure]
       | rw [queries_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr; intro x)
    | (exact erase_pure _)
    | rfl
    | split

theorem preparation_run_value (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (view : verifier.View) (hash : H) (scratch : Array aspis_core.field.WideExact 29#usize) :
    (run (PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash scratch)).2=
      OriginalPreparedNative.prepare (withQueries B Q) D sem view hash scratch := by
  rw [run_value,preparation_erasure]

#print axioms preparation_erasure
#print axioms preparation_run_value
end AspisR1PublicPreparation.PreparedHashCode
