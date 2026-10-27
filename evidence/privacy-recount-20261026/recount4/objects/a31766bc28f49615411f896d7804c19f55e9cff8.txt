import R1Z.ProverRwQueryMaterial
import R1Z.ProverRwQueryPolicy
set_option autoImplicit false
namespace R1Z.ProverRwQueryMaterialTransport
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan ProverRwQueryMaterial
variable [ExternalTypes] [ExternalFuns]

abbrev OldState := AspisR1SimControl21.transcript.control21.Transcript

def erase {H : Type} (s : OldState H Unit) : host_transcript.Transcript H :=
  ⟨s.state,s.hash⟩

def hash {H : Type} (h : aspis_core.digest.Digest32 H) :
    AspisR1SimControl21.aspis_core.digest.Digest32 H :=
  ⟨h.coremarkerCopyInst,h.digest⟩

set_option backward.isDefEq.respectTransparency false in
theorem absorb_transport {H : Type} (h : aspis_core.digest.Digest32 H)
    (s : OldState H Unit) (row : U8) (payload : Slice U8) :
    host_transcript.Transcript.absorb h (erase s) row payload =
      (AspisR1SimControl21.transcript.control21.Transcript.absorb
        (hash h) ProverCommitQuery26.policy s row payload >>= fun v => ok (erase v)) := by
  simp only [host_transcript.Transcript.absorb,
    AspisR1SimControl21.transcript.control21.Transcript.absorb,
    hash,erase,lift,bind_tc_ok,bind_assoc_eq]

set_option backward.isDefEq.respectTransparency false in
theorem materialize_transport {H : Type} (h : aspis_core.digest.Digest32 H)
    (s : OldState H Unit) (row : U8) (payload : Slice U8) :
    materialize h (erase s) row payload =
      (ProverCommitQuery26.materialize (hash h) ProverCommitQuery26.policy s row payload >>=
        fun p => ok (erase p.1,p.2)) := by
  unfold materialize materializeK
  rw [absorb_transport]
  simp only [ProverCommitQuery26.materialize,hash,bind_assoc_eq,bind_tc_ok,lift]
  repeat'
    try rw [bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro v hv
    try (change (_ × _) at v; rcases v with ⟨v1,v2⟩)
    try dsimp only [erase,Aeneas.Std.uncurry]
    try simp only [bind_assoc_eq,bind_tc_ok,lift]

#print axioms absorb_transport
#print axioms materialize_transport
end R1Z.ProverRwQueryMaterialTransport
