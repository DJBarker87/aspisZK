import R1Z.ProverRwQueryPublish
set_option autoImplicit false
namespace R1Z.ProverRwQueryCallerSplit
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwQueryMaterial ProverRwQueryPublish
variable [ExternalTypes] [ExternalFuns]

set_option backward.isDefEq.respectTransparency false in
theorem queries_factor {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    host_transcript.Transcript.queries hash self row payload =
      (materialize hash self row payload >>= fun p => do
        let r ← host_transcript.queries_from_pairs p.2.1 p.2.2
        publish p.1 r) := by
  rw [materialize_bind hash self row payload (fun s b a => host_transcript.queries_from_pairs b a >>= publish s)]
  simp only [host_transcript.Transcript.queries, materializeK, lift, bind_tc_ok]
  repeat'
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro v hv
    try (change (_ × _) at v; rcases v with ⟨v1,v2⟩)
    try dsimp only
  exact branch_publish _ _

#print axioms queries_factor
end R1Z.ProverRwQueryCallerSplit
