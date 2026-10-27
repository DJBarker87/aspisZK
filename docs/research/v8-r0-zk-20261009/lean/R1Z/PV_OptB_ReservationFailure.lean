import R1Z.PV_OptB_SourceRetryStep
set_option autoImplicit false
namespace R1Z.PV_OptB_ReservationFailure
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]
abbrev MaskError := aspis_prover.state_only_hiding.StateOnlyMaskBuildError
abbrev Material := aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
  aspis_prover.state_only_hiding.StateOnlyMaskMaterial
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext

/-- Errors of the actual pre-compilation reservation/material prefix stop
before any private compiled trace is inspected. This covers a named prefix,
not witness-independent reachability of later reservations. -/
theorem prefix_error {S : Type}
    (ledger : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (context : Context)
    (binding : Array U8 32#usize) (secret : Secret) (store after : S)
    (raw : MaskError) (e : verifier.Error)
    (returned : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      ledger secret hash binding context store = .ok (.Err raw,after))
    (mapped : core.result.Result.map_err (T := Material) (BuiltinFnOnce MaskError verifier.Error)
      (.Err raw) prover.mask_error = .ok (.Err e)) :
    prover.prove_masked_with_attempt ledger pub compiled .S2 hash context binding secret store =
      .ok (.Err e,after) := by
  rw [prover.prove_masked_with_attempt,returned]
  simp only [bind_tc_ok,Aeneas.Std.uncurry,mapped,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

#print axioms prefix_error
end R1Z.PV_OptB_ReservationFailure
