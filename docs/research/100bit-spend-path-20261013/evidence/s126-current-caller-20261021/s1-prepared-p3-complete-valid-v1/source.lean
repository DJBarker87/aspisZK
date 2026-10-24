import S1PreparedP3ScalarQueriesValidV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result ControlFlow
open AspisV8R19.DuplexFrames S4SolanaDigestP3RegroupV1

/-- Derived for every complete preparation input; no per-call association,
independent child success or desired trace equality is an assumption. -/
theorem preparation_p3_valid (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries)
    {H : Type} (copy : core.marker.Copy H) (sha : Bytes → Array U8 32#usize)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    OracleValid sha (PreparedSourceEffects.prepare (preparationEffects B Q)
      (solanaDigestP3Model copy sha) sem view hash scratch) := by
  unfold PreparedSourceEffects.prepare preparationEffects
  repeat' first
    | (solve | apply new_p3_valid)
    | (solve | apply scalar_p3_valid)
    | (solve | apply scalar_k_p3_valid)
    | (solve | apply queries_p3_valid)
    | (solve | apply valid_lift)
    | (solve | apply valid_pure)
    | apply valid_bind
    | intro x
    | split

#print axioms preparation_p3_valid
end AspisR1PublicPreparation.PreparedHashCode
