import AspisR1ProverCommit.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.ProverCommitSaltSource
open AspisR1ProverCommit
abbrev Reserved := aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Bytes32 := Aeneas.Std.Array U8 32#usize
abbrev Hash := Slice (Slice U8) → Result Bytes32

def saltSlices (binding nonce secret : Bytes32) (tag : U8) (index : U32) : Slice (Slice U8) :=
  Aeneas.Std.Array.to_slice (Aeneas.Std.Array.make 6#usize [
    aspis_prover.state_only_entropy.LEAF_SALT_DOMAIN,
    Aeneas.Std.Array.to_slice binding,
    Aeneas.Std.Array.to_slice nonce,
    Aeneas.Std.Array.to_slice (Aeneas.Std.Array.make 1#usize [tag]),
    Aeneas.Std.Array.to_slice (core.num.U32.to_le_bytes index),
    Aeneas.Std.Array.to_slice secret])

/-- Exact callback slices of the extracted per-leaf method, conditional only
on the separately named successful validation and binding computations.
The hash is arbitrary; no concrete hash evaluation is used. -/
theorem salt_source (self : Reserved) (hash : Hash) (context : Context)
    (tag : U8) (index : U32) (binding : Bytes32)
    (valid : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.validate_pool_v1_context self context = ok (.Ok ()))
    (bound : aspis_prover.state_only_entropy.pool_v1_private_attempt_binding
      hash self.precommit_binding context = ok binding) :
    aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt self hash context tag index = (do
      let answer ← hash (saltSlices binding self.mask_nonce self.leaf_salt_seed tag index)
      ok (.Ok answer)) := by
  simp [aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_leaf_salt, valid, bound, saltSlices,
    core.result.Result.Insts.CoreOpsTry.branch,
    zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref,
    Array.Insts.CoreConvertAsRefSlice.as_ref, lift]
  rfl

#print axioms salt_source
end R1Z.ProverCommitSaltSource
