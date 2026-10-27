import R1Z.PV_RE_BindTransportB10
import R1Z.ProverRwOuterAfterChecks
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AfterPrefix1000
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
    (context : Context) (store : S) :
    ∃ next, ProverRwOuterAfterChecks.afterChecks inst secret hash binding context store =
      (inst.reserve store context.statement_digest context.mask_nonce >>= next) := by
  unfold ProverRwOuterAfterChecks.afterChecks
  exact ⟨_,rfl⟩
#print axioms entered
end R1Z.PV_RE_AfterPrefix1000
