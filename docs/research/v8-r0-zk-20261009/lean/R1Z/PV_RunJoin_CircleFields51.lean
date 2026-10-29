import R1Z.PV_RunJoin_CircleReach51
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CircleFields51
open Aeneas Aeneas.Std Result ProverRwFull

theorem first [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_wire.SemanticTranscript H) (framed : Slice U8) (p : aspis_core.circle.SecureCirclePoint)
    (h : host_wire.SemanticTranscript.challenge_reference_circle_point D t 25#u8 framed=ok (.Ok p,next)) :
    t.next_row=25#u8 ∧ next.hash=t.hash ∧ next.next_row=26#u8 := by
  obtain ⟨b,hs,hp⟩ := PV_RunJoin_CircleReach51.first D t next framed p h
  obtain ⟨ordered,same,counter⟩ := PV_RunJoin_SemanticBlockFields51.complete D t next 25#u8 framed b hs
  exact ⟨ordered.symm,same,counter.trans rfl⟩

theorem second [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_wire.SemanticTranscript H) (framed : Slice U8) (p : aspis_core.circle.SecureCirclePoint)
    (h : host_wire.SemanticTranscript.challenge_reference_circle_point D t 26#u8 framed=ok (.Ok p,next)) :
    t.next_row=26#u8 ∧ next.hash=t.hash ∧ next.next_row=27#u8 := by
  obtain ⟨b,hs,hp⟩ := PV_RunJoin_CircleReach51.second D t next framed p h
  obtain ⟨ordered,same,counter⟩ := PV_RunJoin_SemanticBlockFields51.complete D t next 26#u8 framed b hs
  exact ⟨ordered.symm,same,counter.trans rfl⟩
#print axioms first
#print axioms second
end R1Z.PV_RunJoin_CircleFields51
