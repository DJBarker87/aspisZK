import R1Z.PV_RunJoin_SemanticBlockReach51
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticBlockFields51
open Aeneas Aeneas.Std Result ProverRwFull

theorem validated [ExternalTypes] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) (b : Array U8 32#usize)
    (h : host_wire.SemanticTranscript.sample_block_validated D t row framed=ok (.Ok b,next)) :
    row=t.next_row ∧ next.hash=t.hash ∧ next.next_row=U8.wrapping_add row 1#u8 := by
  rw [PV_RunJoin_SemanticRequests51.source] at h
  split at h
  · cases h
  · rename_i ordered
    have eq : row=t.next_row := by simpa only [bne_iff_ne,not_not] using ordered
    obtain ⟨absorbed,ha,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨block,hb,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨advanced,had,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    have same := Result.ok.inj h
    cases same
    exact ⟨eq,rfl,by rw [eq]⟩

theorem complete [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) (b : Array U8 32#usize)
    (h : host_wire.SemanticTranscript.sample_block D t row framed=ok (.Ok b,next)) :
    row=t.next_row ∧ next.hash=t.hash ∧ next.next_row=U8.wrapping_add row 1#u8 := by
  obtain ⟨ordered,payload,hp,hs⟩ := PV_RunJoin_SemanticBlockReach51.complete D t next row framed b h
  exact validated D t next row framed b hs
#print axioms validated
#print axioms complete
end R1Z.PV_RunJoin_SemanticBlockFields51
