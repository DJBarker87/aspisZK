import R1Z.ProverRwEntropyHalves
import R1Z.ProverRwEffectOwner
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyNonceGuard64
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwEffectOwner ProverRwEffectTape
variable [ExternalTypes] [ExternalFuns]

/-- Discharges the source nonce-test premise, retaining the complete world
and recording zero calls. The world interpreter's native adequacy is separate. -/
theorem zero_nonce (nonce : Array U8 32#usize)
    (zero : ProverCommitOwnerBytes42.block nonce = 0) (world : World) :
    worldOwner nonce world = ⟨.returned (.ok (.Err .RepeatedZeroBlock)),world⟩ := by
  apply rejected_nonce
  rw [ProverRwEntropyHalves.nonzero_block]
  simp only [zero,decide_true,Bool.not_true]

theorem nonzero_nonce (nonce : Array U8 32#usize)
    (nonzero : ProverCommitOwnerBytes42.block nonce ≠ 0) (world : World) :
    worldOwner nonce world = ProverRwEffectTape.run nonce
      aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT 17 0#usize world := by
  unfold worldOwner
  rw [ProverRwEntropyHalves.nonzero_block]
  simp only [nonzero,decide_false,Bool.not_false]

#print axioms zero_nonce
#print axioms nonzero_nonce
end R1Z.ProverRwEntropyNonceGuard64
