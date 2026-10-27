import R1Z.PV_RE_BindTransportB10
import R1Z.ProverRwOuterAfterChecks
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AfterPrefix1007
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Material := aspis_prover.state_only_hiding.StateOnlyMaskMaterial
abbrev Pre := aspis_prover.state_only_entropy.PreReservedNonce
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev Z := Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
theorem entered {S : Type} (inst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secrets) (hash : Hash) (binding : Array U8 32#usize)
    (context : Context) (store : S)
    (store1 : S) (h0 : inst.reserve store context.statement_digest context.mask_nonce = .ok (true,store1))
    (entropy : Array U8 32#usize) (h1 : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy = .ok entropy)
    (material : Material) (h2 : aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore hash binding context entropy ({statement_digest := context.statement_digest,mask_nonce := context.mask_nonce,consumed := false} : Pre) = .ok (.Ok material,({statement_digest := context.statement_digest,mask_nonce := context.mask_nonce,consumed := true} : Pre)))
    (encoded : Array U8 81#usize) (h3 : aspis_core.state_only_hiding.StateOnlyHidingContext.encode context = .ok encoded)
    (borrowed : Slice U8) (h4 : zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref (Array.Insts.CoreConvertAsRefSlice U8 32#usize) Z secret.field_mask_entropy = .ok borrowed)
    (seed : Array U8 32#usize) (h5 : hash (Array.to_slice (Array.make 4#usize [aspis_prover.state_only_entropy.POOL_V1_SOURCE_SEED_DOMAIN,Array.to_slice binding,Array.to_slice encoded,borrowed])) = .ok seed)
    (wrapped : zeroize.Zeroizing (Array U8 32#usize)) (h6 : zeroize.Zeroizing.new Z seed = .ok wrapped) :
    ∃ next, ProverRwOuterAfterChecks.afterChecks inst secret hash binding context store =
      (zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize Z secret.field_mask_entropy >>= next) := by
  unfold ProverRwOuterAfterChecks.afterChecks
  change ∃ next, (inst.reserve store context.statement_digest context.mask_nonce >>= _) = _
  rw [h0]
  change ∃ next, (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy >>= _) = _
  rw [h1]
  change ∃ next, (aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore hash binding context entropy ({statement_digest := context.statement_digest,mask_nonce := context.mask_nonce,consumed := false} : Pre) >>= _) = _
  rw [h2]
  change ∃ next, (aspis_core.state_only_hiding.StateOnlyHidingContext.encode context >>= _) = _
  rw [h3]
  change ∃ next, (zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref (Array.Insts.CoreConvertAsRefSlice U8 32#usize) Z secret.field_mask_entropy >>= _) = _
  rw [h4]
  change ∃ next, (hash (Array.to_slice (Array.make 4#usize [aspis_prover.state_only_entropy.POOL_V1_SOURCE_SEED_DOMAIN,Array.to_slice binding,Array.to_slice encoded,borrowed])) >>= _) = _
  rw [h5]
  change ∃ next, (zeroize.Zeroizing.new Z seed >>= _) = _
  rw [h6]
  exact ⟨_,rfl⟩
#print axioms entered
end R1Z.PV_RE_AfterPrefix1007
