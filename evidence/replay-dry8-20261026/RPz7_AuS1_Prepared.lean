import RPz7_AuS1_Sampling
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Prepared
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1PublicPreparation.PreparedHashCode AuS1_Association AuS1_Hash AuS1_Sampling

theorem control (e : PreparedSourceEffects.Effects Code)
    {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (hn : ∀ h state variant, Uniform hashv (e.newTranscript D h state variant))
    (hs : ∀ t row payload nz, Uniform hashv (e.scalar D t row payload nz))
    (hb : ∀ x, Uniform hashv (e.toBytes x))
    (hq : ∀ t row payload, Uniform hashv (e.queries D t row payload))
    (hr : ∀ t row payload, Uniform hashv (e.rho D t row payload))
    (hp : ∀ n x, Uniform hashv (e.powers n x))
    (hc : ∀ sem y inactive powers kappa, Uniform hashv (e.claim D sem y inactive powers kappa))
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    Uniform hashv (PreparedSourceEffects.prepare e D sem view hash scratch) := by
  unfold PreparedSourceEffects.prepare
  repeat' first
    | (solve | apply hn)
    | (solve | apply hs)
    | (solve | apply hb)
    | (solve | apply hq)
    | (solve | apply hr)
    | (solve | apply hp)
    | (solve | apply hc)
    | (solve | apply lift_uniform)
    | (solve | apply pure_uniform)
    | apply bind_uniform
    | intro x
    | split

 theorem uniform (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (law : ∀ h parts, D.digest h parts = hashv parts)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    Uniform hashv (PreparedSourceEffects.prepare (preparationEffects B Q) D sem view hash scratch) := by
  apply control
  · exact fun h s v => new_uniform D hashv law h s v
  · exact fun t r p n => scalar_uniform B.sampling D hashv law t r p n
  · intro x; apply lift_uniform
  · exact fun t r p => queries_uniform Q D hashv law t r p
  · exact fun t r p => rho_uniform B.sampling D hashv law t r p
  · intro n x; apply lift_uniform
  · intro sem y inactive powers kappa; apply lift_uniform

#print axioms control
#print axioms uniform
end AspisR1.AuS1_Prepared
end
