import R1Z.PV_RunJoin_SemanticSampler51
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticSourceSuccess51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitSubfieldOps47
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (t next : host_wire.SemanticTranscript H)
    (row : U8) (framed : Slice U8) (q : ProverRwFull.aspis_core.field.QM31)
    (h : @host_wire.SemanticTranscript.semantic (types base) (selected base heap box ops) H D t row framed=
      ok (.Ok q,next)) :
    ∃ b : Array U8 32#usize,
      @host_wire.SemanticTranscript.sample_block (types base) (selected base heap box ops) H D t row framed=
        ok (.Ok b,next) ∧
      @ProverRwFull.sampler.qm31_sample (types base) (selected base heap box ops) b=ok q ∧
      Canonical (PV_RunJoin_SemanticScalar50.raw q) ∧
      ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode (PV_RunJoin_SemanticScalar50.raw q))=
        PhaseSamplerParserBin.scalar (PV_RunJoin_OpeningBlock50.answer b) := by
  unfold host_wire.SemanticTranscript.semantic at h
  split at h
  · cases h
  · obtain ⟨⟨status,after⟩,hs,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    dsimp only [Aeneas.Std.uncurry] at h
    cases status with
    | Err e =>
      change (ok ((core.result.Result.Err e : core.result.Result ProverRwFull.aspis_core.field.QM31 r1_wire.Error),after))=ok (.Ok q,next) at h
      cases h
    | Ok b =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨actual,ha,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      have eq := Result.ok.inj h
      cases eq
      obtain ⟨produced,hp,hc,hm⟩ := PV_RunJoin_SemanticSampler51.complete base heap box ops (PV_RunJoin_OpeningBlock50.answer b)
      rw [PV_RunJoin_OpeningBlock50.roundtrip] at hp
      have same : actual=produced := Result.ok.inj (ha.symm.trans hp)
      cases same
      exact ⟨b,hs,ha,hc,hm⟩
#print axioms complete
end R1Z.PV_RunJoin_SemanticSourceSuccess51
