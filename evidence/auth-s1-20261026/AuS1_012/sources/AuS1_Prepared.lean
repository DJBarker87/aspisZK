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
    | (solve | exact new_uniform D hashv law _ _ _)
    | (solve | exact scalar_uniform B.sampling D hashv law _ _ _ _)
    | (solve | exact rho_uniform B.sampling D hashv law _ _ _)
    | (solve | exact queries_uniform Q D hashv law _ _ _)
    | (solve | with_reducible apply lift_uniform)
    | (solve | with_reducible apply pure_uniform)
    | (solve | exact digest_uniform hashv D _ _ (law _ _))
    | (solve | trivial)
    | with_reducible apply bind_uniform
    | intro x
    | split

#print axioms uniform
end AspisR1.AuS1_Prepared
end
