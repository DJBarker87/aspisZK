import R1Z.ProverRwOuterAfterChecks
import R1Z.ProverRwRetryModel
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ReservationGuards
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_ResultPost
variable [ExternalTypes] [ExternalFuns]

abbrev MaterialStatus := core.result.Result
  (aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets ×
    aspis_prover.state_only_hiding.StateOnlyMaskMaterial)
  aspis_prover.state_only_hiding.StateOnlyMaskBuildError

/-- Verbatim source guard order before the single durable-store callback. -/
def guarded {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secret) (hash : Hash) (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : S) :
    Result (MaterialStatus × S) := do
  let different ← core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 context.mask_nonce secret.mask_nonce
  if different then .ok (.Err .Layout,s) else
    let mask ← aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1
    if context.mask_layout_fingerprint != mask then .ok (.Err .Layout,s) else
      let factor ← aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1
      if context.layout_factor_fingerprint != factor then .ok (.Err .Layout,s) else
        ProverRwOuterAfterChecks.afterChecks store secret hash binding context s

theorem source_eq {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secret) (hash : Hash) (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : S) :
    guarded store secret hash binding context s =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
        store secret hash binding context s := by
  unfold guarded ProverRwOuterAfterChecks.afterChecks
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  rfl

theorem preserves {S : Type} (P : S → Prop)
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secret) (hash : Hash) (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : S)
    (initial : P s)
    (after : Post (fun out => P out.2)
      (ProverRwOuterAfterChecks.afterChecks store secret hash binding context s)) :
    Post (fun out => P out.2) (guarded store secret hash binding context s) := by
  unfold guarded
  apply bind_right
  intro different
  split
  · exact PV_RunJoin_ResultPost.ok _ _ initial
  · apply bind_right
    intro mask
    split
    · exact PV_RunJoin_ResultPost.ok _ _ initial
    · apply bind_right
      intro factor
      split
      · exact PV_RunJoin_ResultPost.ok _ _ initial
      · exact after

#print axioms source_eq
#print axioms preserves
end R1Z.PV_RunJoin_ReservationGuards
