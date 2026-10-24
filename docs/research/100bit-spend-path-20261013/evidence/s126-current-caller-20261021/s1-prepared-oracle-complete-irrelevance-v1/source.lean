import S1PreparedOracleScalarQueriesIrrelevanceV1
import S1PreparedCompleteHashErasureV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result ControlFlow

private theorem lift_oracle_congr {A : Type} (first second : Result A) (h : first=second) :
    oracleProgram (monadLift first : Code A)=oracleProgram (monadLift second : Code A) := by rw [h]

theorem preparation_oracle_dictionary_irrelevant
    (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H)
    (claimLaw : ∀ sem y1 inactive powers kappa,
      B.claim first sem y1 inactive powers kappa=B.claim second sem y1 inactive powers kappa)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    oracleProgram (PreparedSourceEffects.prepare (preparationEffects B Q) first sem view hash scratch)=
      oracleProgram (PreparedSourceEffects.prepare (preparationEffects B Q) second sem view hash scratch) := by
  unfold PreparedSourceEffects.prepare preparationEffects
  repeat' first
    | (solve | with_reducible rfl)
    | (solve | with_reducible apply new_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply scalar_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply scalar_k_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply queries_oracle_dictionary_irrelevant)
    | (solve
        with_reducible apply lift_oracle_congr
        first | exact claimLaw _ _ _ _ _ | rfl)
    | with_reducible apply oracleProgram_bind_congr
    | intro x
    | split

#print axioms preparation_oracle_dictionary_irrelevant
end AspisR1PublicPreparation.PreparedHashCode
