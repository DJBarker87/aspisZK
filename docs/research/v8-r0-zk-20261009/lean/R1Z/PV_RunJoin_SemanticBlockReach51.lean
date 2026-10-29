import R1Z.PV_RunJoin_SemanticRequests51
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticBlockReach51
open Aeneas Aeneas.Std Result ProverRwFull

theorem complete [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_wire.SemanticTranscript H) (row : U8) (framed : Slice U8) (b : Array U8 32#usize)
    (h : host_wire.SemanticTranscript.sample_block D t row framed=ok (.Ok b,next)) :
    row=t.next_row ∧ ∃ payload,
      host_wire.parse_record row framed=ok (.Ok payload) ∧
      host_wire.SemanticTranscript.sample_block_validated D t row framed=ok (.Ok b,next) := by
  unfold host_wire.SemanticTranscript.sample_block at h
  split at h
  · cases h
  · rename_i ordered
    have eq : row=t.next_row := by simpa only [bne_iff_ne,not_not] using ordered
    obtain ⟨status,hs,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    cases status with
    | Err e =>
      change (ok ((core.result.Result.Err e : core.result.Result (Array U8 32#usize) r1_wire.Error),t))=ok (.Ok b,next) at h
      cases h
    | Ok payload =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      exact ⟨eq,payload,hs,h⟩
#print axioms complete
end R1Z.PV_RunJoin_SemanticBlockReach51
