import R1Z.ProverRwBodyReservationTransport
import R1Z.PV_RunJoin_ReservationGuards
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ReservationFootprint
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_ResultPost
variable [ExternalTypes] [ExternalFuns]

theorem after_checks {S : Type} (P : S → Prop)
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secret) (hash : Hash) (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : S)
    (callback : ∀ accepted after,
      store.«reserve» s context.statement_digest context.mask_nonce = .ok (accepted,after) → P after) :
    Post (fun out => P out.2) (ProverRwOuterAfterChecks.afterChecks store secret hash binding context s) := by
  intro out run
  cases reply : store.«reserve» s context.statement_digest context.mask_nonce with
  | fail e =>
    simp only [ProverRwOuterAfterChecks.afterChecks,reply,bind_tc_fail] at run
    cases run
  | div =>
    simp only [ProverRwOuterAfterChecks.afterChecks,reply,bind_tc_div] at run
    cases run
  | ok pair =>
    have kept := ProverRwBodyReservationTransport.callback_writeback store secret hash binding context
      s pair.2 pair.1 reply
    rw [run] at kept
    change out.2 = pair.2 at kept
    rw [kept]
    exact callback pair.1 pair.2 reply

/-- The exact emitted guard stage either retains the initial state or writes
back the one entered reservation callback. No native effect law is assumed
for proving this SOURCE control theorem. -/
theorem reserve_build {S : Type} (P : S → Prop)
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secret) (hash : Hash) (binding : Array U8 32#usize)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (s : S)
    (initial : P s)
    (callback : ∀ accepted after,
      store.«reserve» s context.statement_digest context.mask_nonce = .ok (accepted,after) → P after) :
    Post (fun out => P out.2)
      (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
        store secret hash binding context s) := by
  rw [← PV_RunJoin_ReservationGuards.source_eq]
  exact PV_RunJoin_ReservationGuards.preserves P store secret hash binding context s initial
    (after_checks P store secret hash binding context s callback)

#print axioms after_checks
#print axioms reserve_build
end R1Z.PV_RunJoin_ReservationFootprint
