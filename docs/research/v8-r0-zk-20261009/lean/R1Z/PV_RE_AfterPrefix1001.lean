import R1Z.PV_RE_BindTransport10
import R1Z.ProverRwOuterAfterChecks
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AfterPrefix1001
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Material := aspis_prover.state_only_hiding.StateOnlyMaskMaterial
abbrev Pre := aspis_prover.state_only_entropy.PreReservedNonce
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev Z := Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
theorem prefix {S : Type} (inst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secrets) (hash : Hash) (binding : Array U8 32#usize)
    (context : Context) (store : S)
    (store1 : S) (h0 : inst.reserve store context.statement_digest context.mask_nonce = .ok (true,store1)) :
    ∃ next, ProverRwOuterAfterChecks.afterChecks inst secret hash binding context store =
      (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy >>= next) := by
  unfold ProverRwOuterAfterChecks.afterChecks
  change ∃ next, (inst.reserve store context.statement_digest context.mask_nonce >>= _) = _
  rw [h0]
  exact ⟨_,rfl⟩
#print axioms prefix
end R1Z.PV_RE_AfterPrefix1001
