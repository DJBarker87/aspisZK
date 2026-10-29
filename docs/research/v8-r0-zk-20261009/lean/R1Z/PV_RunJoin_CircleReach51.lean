import R1Z.PV_RunJoin_SemanticBlockFields51
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CircleReach51
open Aeneas Aeneas.Std Result ProverRwFull

theorem first [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_wire.SemanticTranscript H) (framed : Slice U8) (p : aspis_core.circle.SecureCirclePoint)
    (h : host_wire.SemanticTranscript.challenge_reference_circle_point D t 25#u8 framed=ok (.Ok p,next)) :
    ∃ b : Array U8 32#usize,
      host_wire.SemanticTranscript.sample_block D t 25#u8 framed=ok (.Ok b,next) ∧
      sampler.circle_sample b aspis_core.r0_transcript.CircleRow.First=ok p := by
  simp only [host_wire.SemanticTranscript.challenge_reference_circle_point] at h
  obtain ⟨⟨status,after⟩,hb,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  dsimp only [Aeneas.Std.uncurry] at h
  cases status with
  | Err e =>
    change (ok ((core.result.Result.Err e : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),after))=ok (.Ok p,next) at h
    cases h
  | Ok b =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨point,hp,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    have eq := Result.ok.inj h
    cases eq
    exact ⟨b,hb,hp⟩

theorem second [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (t next : host_wire.SemanticTranscript H) (framed : Slice U8) (p : aspis_core.circle.SecureCirclePoint)
    (h : host_wire.SemanticTranscript.challenge_reference_circle_point D t 26#u8 framed=ok (.Ok p,next)) :
    ∃ b : Array U8 32#usize,
      host_wire.SemanticTranscript.sample_block D t 26#u8 framed=ok (.Ok b,next) ∧
      sampler.circle_sample b aspis_core.r0_transcript.CircleRow.Second=ok p := by
  simp only [host_wire.SemanticTranscript.challenge_reference_circle_point] at h
  obtain ⟨⟨status,after⟩,hb,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  dsimp only [Aeneas.Std.uncurry] at h
  cases status with
  | Err e =>
    change (ok ((core.result.Result.Err e : core.result.Result aspis_core.circle.SecureCirclePoint r1_wire.Error),after))=ok (.Ok p,next) at h
    cases h
  | Ok b =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨point,hp,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    have eq := Result.ok.inj h
    cases eq
    exact ⟨b,hb,hp⟩
#print axioms first
#print axioms second
end R1Z.PV_RunJoin_CircleReach51
