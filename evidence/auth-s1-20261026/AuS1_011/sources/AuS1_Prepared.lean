import AuS1_Sampling
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Prepared
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Association AuS1_Hash AuS1_Sampling

theorem uniform (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    Uniform hashv (PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash scratch) := by
  unfold PreparedSourceEffects.prepare
  repeat' first
    | (solve | with_reducible apply new_uniform; assumption)
    | (solve | with_reducible apply scalar_uniform; assumption)
    | (solve | with_reducible apply rho_uniform; assumption)
    | (solve | with_reducible apply queries_uniform; assumption)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | with_reducible apply bind_uniform
    | intro x
    | split

#print axioms uniform
end AspisR1.AuS1_Prepared
end
