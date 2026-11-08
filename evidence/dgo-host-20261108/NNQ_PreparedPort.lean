import NNQ_DSim
noncomputable section
set_option autoImplicit false
open AspisR1.NNQ_HostDigest
namespace AspisR1PublicPreparation.PreparedHashCode.NNQ_Port
open Aeneas Aeneas.Std Result

theorem new_oracle_dictionary_irrelevant {H : Type} (first second : aspis_core.Digest32 H)
    (hash : H) (state : Array U8 32#usize) (variant : transport.Variant) :
    DSim (PreparedHashEffects.new effects first hash state variant) (PreparedHashEffects.new effects second hash state variant) := by
  unfold PreparedHashEffects.new
  repeat' first
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem absorb_oracle_dictionary_irrelevant {H : Type} (first second : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    DSim (PreparedHashEffects.absorb effects first self row payload) (PreparedHashEffects.absorb effects second self row payload) := by
  unfold PreparedHashEffects.absorb
  repeat' first
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem block_oracle_dictionary_irrelevant {H : Type} (first second : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    DSim (PreparedHashEffects.block effects first self row payload) (PreparedHashEffects.block effects second self row payload) := by
  unfold PreparedHashEffects.block
  repeat' first
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible apply absorb_oracle_dictionary_irrelevant)
    | (solve | with_reducible exact dsim_digest _ _ _ _)
    | with_reducible apply dsim_bind
    | intro x
    | split

#print axioms new_oracle_dictionary_irrelevant
#print axioms absorb_oracle_dictionary_irrelevant
#print axioms block_oracle_dictionary_irrelevant
end AspisR1PublicPreparation.PreparedHashCode.NNQ_Port
set_option autoImplicit false
open AspisR1.NNQ_HostDigest
namespace AspisR1PublicPreparation.PreparedHashCode.NNQ_Port
open Aeneas Aeneas.Std Result ControlFlow

theorem digest_oracle_dictionary_irrelevant {H : Type} (first second : aspis_core.Digest32 H)
    (hash : H) (parts : Slice (Slice U8)) :
    DSim (effects.digest first hash parts) (effects.digest second hash parts) := dsim_digest _ _ _ _

private theorem query_error_program_irrelevant {H : Type} (first second : aspis_core.Digest32 H)
    (x : core.result.Result (Array U32 22#usize × Array U8 32#usize) aspis_core.transcript.QuerySampleError) :
    DSim (monadLift (core.result.Result.map_err
      (transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError first) x ()) :
        Code (core.result.Result (Array U32 22#usize × Array U8 32#usize) verifier.Error)) (monadLift (core.result.Result.map_err
      (transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError second) x ()) :
        Code (core.result.Result (Array U32 22#usize × Array U8 32#usize) verifier.Error)) := by
  have same : transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError first =
      transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError second := dsim_digest _ _ _ _
  rw [same]
  exact dsim_refl _

theorem scalar_oracle_dictionary_irrelevant (B : PreparedModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (nonzero : Bool) :
    DSim (PreparedScalarEffects.scalar effects B first self row payload nonzero) (PreparedScalarEffects.scalar effects B second self row payload nonzero) := by
  unfold PreparedScalarEffects.scalar
  repeat' first
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible apply block_oracle_dictionary_irrelevant)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem scalar_k_oracle_dictionary_irrelevant (B : PreparedModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    DSim (PreparedScalarEffects.scalar_k effects B first self row payload) (PreparedScalarEffects.scalar_k effects B second self row payload) := by
  unfold PreparedScalarEffects.scalar_k
  repeat' first
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible apply block_oracle_dictionary_irrelevant)
    | with_reducible apply dsim_bind
    | intro x
    | split

theorem queries_oracle_dictionary_irrelevant (Q : QueriesModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    DSim (PreparedQueryEffects.queries effects Q first self row payload) (PreparedQueryEffects.queries effects Q second self row payload) := by
  unfold PreparedQueryEffects.queries
  repeat' first
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible apply absorb_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply digest_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply query_error_program_irrelevant)
    | with_reducible apply dsim_bind
    | intro x
    | split

#print axioms digest_oracle_dictionary_irrelevant
#print axioms scalar_oracle_dictionary_irrelevant
#print axioms scalar_k_oracle_dictionary_irrelevant
#print axioms queries_oracle_dictionary_irrelevant
end AspisR1PublicPreparation.PreparedHashCode.NNQ_Port
set_option autoImplicit false
open AspisR1.NNQ_HostDigest
namespace AspisR1PublicPreparation.PreparedHashCode.NNQ_Port
open Aeneas Aeneas.Std Result ControlFlow

private theorem lift_oracle_congr {A : Type} (first second : Result A) (h : first=second) :
    DSim (monadLift first : Code A) (monadLift second : Code A) := by rw [h]; exact dsim_refl _

theorem preparation_oracle_dictionary_irrelevant
    (B : PreparedScratchModel.Boundaries) (Q : QueriesModel.Boundaries) {H : Type}
    (first second : aspis_core.Digest32 H)
    (claimLaw : ∀ sem y1 inactive powers kappa,
      B.claim first sem y1 inactive powers kappa=B.claim second sem y1 inactive powers kappa)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (scratch : Array aspis_core.field.WideExact 29#usize) :
    DSim (PreparedSourceEffects.prepare (preparationEffects B Q) first sem view hash scratch) (PreparedSourceEffects.prepare (preparationEffects B Q) second sem view hash scratch) := by
  unfold PreparedSourceEffects.prepare preparationEffects
  repeat' first
    | (solve | with_reducible exact dsim_refl _)
    | (solve | with_reducible apply new_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply scalar_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply scalar_k_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply queries_oracle_dictionary_irrelevant)
    | (solve | with_reducible apply lift_oracle_congr
               first | exact claimLaw _ _ _ _ _ | rfl)
    | with_reducible apply dsim_bind
    | intro x
    | split

#print axioms preparation_oracle_dictionary_irrelevant
end AspisR1PublicPreparation.PreparedHashCode.NNQ_Port
end
