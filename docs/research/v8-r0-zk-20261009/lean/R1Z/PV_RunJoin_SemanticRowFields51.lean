import R1Z.PV_RunJoin_SemanticRowReach51
import R1Z.PV_RunJoin_SemanticSourceSuccess51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticRowFields51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H) (row : U8) (payload : Slice U8)
    (t next : host_wire.SemanticTranscript H) (out bytes : alloc.vec.Vec U8) (q : aspis_core.field.QM31)
    (h : @host_semantic.semantic_row (types base) (selected base heap box ops) H D row payload t out=ok (.Ok q,next,bytes)) :
    row=t.next_row ∧ next.hash=t.hash ∧ next.next_row=U8.wrapping_add row 1#u8 ∧
    ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw q) ∧
    ∃ (framed : alloc.vec.Vec U8) (b : Array U8 32#usize),
      @host_wire.record (types base) (selected base heap box ops) row payload=ok (.Ok framed) ∧
      @host_wire.SemanticTranscript.sample_block (types base) (selected base heap box ops) H D t row
        (alloc.vec.Vec.deref framed)=ok (.Ok b,next) ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (alloc.vec.Vec.deref framed)=ok bytes ∧
      ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode (PV_RunJoin_SemanticScalar50.raw q))=
        PhaseSamplerParserBin.scalar (PV_RunJoin_OpeningBlock50.answer b) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨framed,hr,hs,ha⟩ := PV_RunJoin_SemanticRowReach51.complete D row payload t next out bytes q h
  obtain ⟨b,hb,hq,hc,hm⟩ := PV_RunJoin_SemanticSourceSuccess51.complete base heap box ops D t next row (alloc.vec.Vec.deref framed) q hs
  obtain ⟨ordered,same,counter⟩ := PV_RunJoin_SemanticBlockFields51.complete D t next row (alloc.vec.Vec.deref framed) b hb
  exact ⟨ordered,same,counter,hc,framed,b,hr,hb,ha,hm⟩
#print axioms complete
end R1Z.PV_RunJoin_SemanticRowFields51
