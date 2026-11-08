import NNQ_SemanticPort
noncomputable section
open AspisR1.NNQ_HostDigest
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentPreparedClaim.NNQ_Port

theorem prepared_claim_digest_irrelevant {Dot H : Type} (ops : ClaimDotOps Dot)
    (first second : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive : aspis_core.field.WideExact)
    (g : Array aspis_core.field.WideExact 29#usize) (kappa : aspis_core.field.WideExact) :
    verifier.prepared_claim ops first sem y1 inactive g kappa=
      verifier.prepared_claim ops second sem y1 inactive g kappa := by
  unfold verifier.prepared_claim verifier.prepared_claim_loop verifier.prepared_claim_loop.body
    verifier.prepared_claim_dot verifier.prepared_claim_dot_loop verifier.prepared_claim_dot_loop.body
  rfl

#print axioms prepared_claim_digest_irrelevant
end AspisR1CurrentPreparedClaim.NNQ_Port
namespace AspisR1ClaimPreparedBridge.NNQ_Port

theorem claimPublic_digest_irrelevant {H : Type}
    (first second : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE) :
    claimPublic first sem y1 inactive g kappa=claimPublic second sem y1 inactive g kappa := by
  unfold claimPublic
  rw [AspisR1CurrentPreparedClaim.NNQ_Port.prepared_claim_digest_irrelevant _ (toClaimDigest first) (toClaimDigest second)]

#print axioms claimPublic_digest_irrelevant
end AspisR1ClaimPreparedBridge.NNQ_Port

namespace AspisR1CurrentCaller.BorrowedClaimPrepared.NNQ_Port
open Aeneas Aeneas.Std Result AspisR1CurrentCaller AspisR1ClaimPreparedBridge.NNQ_Port
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1PublicPreparation.PreparedHashCode.NNQ_Port
theorem closedPreparation_dictionary_irrelevant {H : Type}
    (first second : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (view : verifier.View) (hash : H) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    DSim (closedPreparationCode first sem view hash scratch) (closedPreparationCode second sem view hash scratch) := by
  unfold closedPreparationCode
  apply dsim_bind
  · apply preparation_oracle_dictionary_irrelevant
    intro sem y1 inactive powers kappa
    exact claimPublic_digest_irrelevant _ _ _ _ _ _ _
  · intro value
    exact dsim_refl _

#print axioms closedPreparation_dictionary_irrelevant
end AspisR1CurrentCaller.BorrowedClaimPrepared.NNQ_Port
namespace AspisR1CurrentCaller.S1PrepareCode.NNQ_Port
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode
open AspisS1ValuesOwnedInstallation BorrowedClaimPrepared.NNQ_Port
private theorem allocation_error_dictionary {H : Type} (first second : aspis_core.digest.Digest32 H) :
    verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError first=
      verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError second := by
  unfold verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
    verifier.candidate.prepare.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  rfl

private theorem semantic_error_dictionary {H : Type} (first second : aspis_core.digest.Digest32 H) :
    verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError first=
      verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError second := by
  unfold verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
    verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  rfl

private theorem semantic_dictionary {H : Type}
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (first second : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) :
    DSim (S1SemanticCodeInstallation.code R B first pub bytes hash) (S1SemanticCodeInstallation.code R B second pub bytes hash) := by
  unfold S1SemanticCodeInstallation.code
  apply dsim_bind
  · apply AspisR1PublicPreparation.S1SemanticCode.NNQ_Port.verify_dictionary_irrelevant
  · intro result
    exact dsim_refl _

theorem dictionary_irrelevant (base : Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (first second : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    DSim (prepare base R B first pub proof hash scratch) (prepare base R B second pub proof hash scratch) := by
  unfold prepare
  repeat' first
    | (solve | with_reducible apply semantic_dictionary)
    | (solve | with_reducible apply closedPreparation_dictionary_irrelevant)
    | (solve | simp only [allocation_error_dictionary first second, semantic_error_dictionary first second]; exact dsim_refl _)
    | (solve | with_reducible exact dsim_refl _)
    | with_reducible apply dsim_if
    | with_reducible apply dsim_bind
    | intro x
    | split

#print axioms allocation_error_dictionary
#print axioms semantic_error_dictionary
#print axioms semantic_dictionary
#print axioms dictionary_irrelevant
end AspisR1CurrentCaller.S1PrepareCode.NNQ_Port
end
