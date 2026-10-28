import R1Z.PV_RDEA_ActualEndpointConsumer
import R1Z.PV_RDEA_ActualDigitLookup
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEA_FocusedReplay
variable [ExternalTypes] [ExternalFuns]
open PV_RDEA_ActualReservationTail

/-- Focused replay through the exact extracted endpoint's SHA prelude and
actual callback tail. This retains the source callback ABI; it does not assert
that the ABI has already acquired the native allocator world. -/
theorem source (self : Store) (nonce : Array U8 32#usize) :
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path self nonce =
      (do let digest ← prelude self nonce; tail self digest) := source_factor self nonce

theorem finite (digest : Array U8 32#usize) (acc : String) :
    aspis_prover.state_only_entropy.reservation_name digest acc 0#usize =
      PV_RDEA_ActualNameLoop.finite digest 32 acc 0#usize :=
  PV_RDEA_ActualNameFinite.start digest acc

#print source
#print axioms source
#print finite
#print axioms finite
#print axioms PV_RDEA_ActualEndpointConsumer.capacity_consumer
#print axioms PV_RDEA_ActualEndpointConsumer.constructor_failure
#print axioms PV_RDEA_ActualDigitLookup.index_length
#print axioms PV_RDEA_ActualReservation.digest_length
end R1Z.PV_RDEA_FocusedReplay
