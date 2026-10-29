import R1Z.PV_RunJoin_SemanticBlockFields51
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticRowReach51
open Aeneas Aeneas.Std Result ProverRwFull

theorem complete [ExternalTypes] [ExternalFuns] {H : Type} (D : aspis_core.digest.Digest32 H)
    (row : U8) (payload : Slice U8) (t next : host_wire.SemanticTranscript H)
    (out bytes : alloc.vec.Vec U8) (q : aspis_core.field.QM31)
    (h : host_semantic.semantic_row D row payload t out=ok (.Ok q,next,bytes)) :
    ∃ framed : alloc.vec.Vec U8,
      host_wire.record row payload=ok (.Ok framed) ∧
      host_wire.SemanticTranscript.semantic D t row (alloc.vec.Vec.deref framed)=ok (.Ok q,next) ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (alloc.vec.Vec.deref framed)=ok bytes := by
  unfold host_semantic.semantic_row at h
  obtain ⟨recorded,hr,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  cases recorded with
  | Err e =>
    change (ok ((core.result.Result.Err e : core.result.Result aspis_core.field.QM31 r1_wire.Error),t,out))=ok (.Ok q,next,bytes) at h
    cases h
  | Ok framed =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
    obtain ⟨⟨status,after⟩,hs,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    dsimp only [Aeneas.Std.uncurry] at h
    cases status with
    | Err e =>
      change (ok ((core.result.Result.Err e : core.result.Result aspis_core.field.QM31 r1_wire.Error),after,out))=ok (.Ok q,next,bytes) at h
      cases h
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨appended,ha,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      have eq := Result.ok.inj h
      cases eq
      exact ⟨framed,hr,hs,ha⟩
#print axioms complete
end R1Z.PV_RunJoin_SemanticRowReach51
