import R1Z.ProverRwOrderedQuerySource
import R1Z.ProverRwOrderedMonad
set_option autoImplicit false
namespace R1Z.ProverRwOrderedQueryErase
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwOrderedOracle
variable [ExternalTypes] [ExternalFuns]

theorem absorb {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (ProverRwOrderedQuerySource.absorb hash self row payload).result=
      host_transcript.Transcript.absorb hash self row payload := by
  simp only [ProverRwOrderedQuerySource.absorb,host_transcript.Transcript.absorb,
    ProverRwOrderedMonad.result_bind,result_native,result_query,result_pure]

theorem materializeK {H A : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8)
    (k : host_transcript.Transcript H → Blocks → Blocks → Execution A) :
    (ProverRwOrderedQuerySource.materializeK hash self row payload k).result=
      ProverRwQueryMaterial.materializeK hash self row payload (fun s b a => (k s b a).result) := by
  simp only [ProverRwOrderedQuerySource.materializeK,ProverRwQueryMaterial.materializeK,
    ProverRwOrderedMonad.result_bind,result_native,result_query,result_pure,absorb]

theorem materialize {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (ProverRwOrderedQuerySource.materialize hash self row payload).result=
      ProverRwQueryMaterial.materialize hash self row payload := by
  simp only [ProverRwOrderedQuerySource.materialize,ProverRwQueryMaterial.materialize,
    materializeK,result_pure]
#print axioms absorb
#print axioms materializeK
#print axioms materialize
end R1Z.ProverRwOrderedQueryErase
