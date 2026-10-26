import R1Z.ProverRwOrderedQueryErase
import R1Z.ProverRwOrderedQueryBounds
import R1Z.ProverRwQueryCallerSplit
set_option autoImplicit false
namespace R1Z.ProverRwOrderedQueries
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwOrderedOracle
variable [ExternalTypes] [ExternalFuns]
-- The history instruments Digest32 calls only. Native publication/TLS remains
-- an explicit, unchanged Result continuation; this is not native view adequacy.
def queries {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    Execution (core.result.Result Queries verifier.Error × host_transcript.Transcript H) := do
  let p ← ProverRwOrderedQuerySource.materialize hash self row payload
  native (do
    let r ← host_transcript.queries_from_pairs p.2.1 p.2.2
    ProverRwQueryPublish.publish p.1 r)

theorem source {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (queries hash self row payload).result=host_transcript.Transcript.queries hash self row payload := by
  rw [ProverRwQueryCallerSplit.queries_factor]
  simp only [queries,ProverRwOrderedMonad.result_bind,
    ProverRwOrderedQueryErase.materialize,result_native]

theorem bound {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (queries hash self row payload).history.length≤17 := by
  unfold queries
  apply ProverRwOrderedBounds.bind_bound (n:=17) (m:=0)
  · exact ProverRwOrderedQueryBounds.materializeK hash self row payload
  · intro p
    exact ProverRwOrderedBounds.native_bound _
#print axioms source
#print axioms bound
end R1Z.ProverRwOrderedQueries
