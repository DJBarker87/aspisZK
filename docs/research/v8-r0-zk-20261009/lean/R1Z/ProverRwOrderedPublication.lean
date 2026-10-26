import R1Z.ProverRwOrderedQueries
set_option autoImplicit false
namespace R1Z.ProverRwOrderedPublication
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Publication, rejection, failure and divergence retain exactly the already
recorded Digest32 requests. The native TLS callback remains uninterpreted. -/
theorem history {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (ProverRwOrderedQueries.queries hash self row payload).history=
      (ProverRwOrderedQuerySource.materialize hash self row payload).history := by
  unfold ProverRwOrderedQueries.queries
  rw [ProverRwOrderedMonad.history_bind]
  cases (ProverRwOrderedQuerySource.materialize hash self row payload).result <;>
    simp [ProverRwOrderedOracle.native]
#print axioms history
end R1Z.ProverRwOrderedPublication
