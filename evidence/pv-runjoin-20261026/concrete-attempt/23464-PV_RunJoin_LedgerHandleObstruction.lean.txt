import R1Z.ProverCommitLedger36
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerHandleObstruction
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitLedger36

/-- A source handle that stays equal cannot by itself encode a fresh native
filesystem reservation. A world/effect state must participate in the decoder. -/
theorem no_handle_only_projection {H : Type} (decode : H → State)
    (before after : H) (same : after = before)
    (schedule : Schedule) (unix : Bool) (path : Path)
    (fresh : path ∉ (decode before).ledger)
    (created : (createNew path
      (schedule (decode before).history.length .create (decode before).history)
      (decode before)).1 = .ok ()) :
    decode after ≠ (reserve schedule unix path (decode before)).2 := by
  intro association
  have retained := reservation_retained schedule unix path (decode before) created
  rw [← association,same] at retained
  exact fresh retained

variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev sourceReserve := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve

/-- Exact obstruction for a FIXED PURE extracted dictionary. The actual native
filesystem produces fresh=true, then duplicate=false, with an unchanged
directory/None source handle. These two source adequacy equations cannot both
hold with that same dictionary and handle. This does not assert that native
Rust violates E2: it identifies the missing explicit effect/world carrier. -/
theorem no_fixed_dictionary_fresh_then_duplicate
    (self : Store) (statement nonce : Array U8 32#usize)
    (first : sourceReserve self statement nonce = .ok (true,self)) :
    sourceReserve self statement nonce ≠ .ok (false,self) := by
  rw [first]
  intro impossible
  cases impossible

#print axioms no_handle_only_projection
#print axioms no_fixed_dictionary_fresh_then_duplicate
end R1Z.PV_RunJoin_LedgerHandleObstruction
