import R1Z.PV_RunJoin_TranscriptAbsorb51
set_option autoImplicit false
namespace R1Z.PV_RunJoin_TranscriptBlock51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_TranscriptRequests51 (Block message)

theorem source [ExternalTypes] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :
    host_transcript.Transcript.block D t row payload=(do
      let absorbed ← D.digest t.hash (PV_RunJoin_TranscriptAbsorb51.request t.state row payload)
      let b ← D.digest t.hash (message absorbed 1#u8)
      let advanced ← D.digest t.hash (message absorbed 2#u8)
      ok (b,{t with state:=advanced})) := by
  rw [PV_RunJoin_TranscriptRequests51.block,PV_RunJoin_TranscriptAbsorb51.source]
  simp only [bind_assoc,bind_tc_ok]

theorem reach [ExternalTypes] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_transcript.Transcript H) (row : U8) (payload : Slice U8) (b : Block)
    (h : host_transcript.Transcript.block D t row payload=ok (b,next)) :
    ∃ absorbed advanced,
      D.digest t.hash (PV_RunJoin_TranscriptAbsorb51.request t.state row payload)=ok absorbed ∧
      D.digest t.hash (message absorbed 1#u8)=ok b ∧
      D.digest t.hash (message absorbed 2#u8)=ok advanced ∧ next={t with state:=advanced} := by
  rw [source] at h
  obtain ⟨absorbed,ha,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  obtain ⟨block,hb,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  obtain ⟨advanced,hadv,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  have eq := Result.ok.inj h
  cases eq
  exact ⟨absorbed,advanced,ha,hb,hadv,rfl⟩
#print axioms source
#print axioms reach
end R1Z.PV_RunJoin_TranscriptBlock51
