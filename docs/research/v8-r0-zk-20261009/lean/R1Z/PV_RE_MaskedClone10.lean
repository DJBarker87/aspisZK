import R1Z.PV_RE_AfterChecksB10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_MaskedClone10
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes]
abbrev Reserved := aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets
abbrev Material := aspis_prover.state_only_hiding.StateOnlyMaskMaterial
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext

theorem entered (ops : ExternalFuns) {S : Type}
    (inst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : Public) (compiled : Compiled) (variant : transport.Variant)
    (hash : Hash) (context : Context) (binding : Array U8 32#usize)
    (secret : Secrets) (store store1 : S) (reserved : Reserved) (material : Material) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ (reservation :
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
        inst secret hash binding context store = .ok (.Ok (reserved,material),store1)),
    ∃ next, prover.prove_masked_with_attempt inst pub compiled variant hash context binding secret store =
      (aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone compiled.semantic_c1 >>= next) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro reservation
  unfold prover.prove_masked_with_attempt
  rw [reservation]
  exact ⟨_,rfl⟩
#print axioms entered
end R1Z.PV_RE_MaskedClone10
