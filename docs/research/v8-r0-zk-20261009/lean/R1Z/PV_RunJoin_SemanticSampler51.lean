import R1Z.PV_RunJoin_SemanticSamplerField51
import R1Z.PV_RunJoin_SemanticScalar50
import R1Z.PV_RunJoin_OpeningByteCodec51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticSampler51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 ProverCommitSubfieldOps47
open R0Z.FsStatement
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (b : OracleAnswer) :
    ∃ q : aspis_core.field.QM31,
      @ProverRwFull.sampler.qm31_sample (types base) (selected base heap box ops) (PV_RunJoin_OpeningSampler50.block b)=ok q ∧
      Canonical (PV_RunJoin_SemanticScalar50.raw q) ∧
      ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode (PV_RunJoin_SemanticScalar50.raw q))=
        PhaseSamplerParserBin.scalar b := by
  obtain ⟨q,hq,hcanonical,hcoordinates⟩ := AspisR1.ExtractedQM31SamplerCorrect.sample_total (PV_RunJoin_OpeningSampler50.block b)
  refine ⟨ProverRwFullSampler.fromSelected (ProverRwSamplerModel.fromOld q),?_,?_,?_⟩
  · change (selected base heap box ops).op248 _=_
    rw [PV_RunJoin_SemanticSamplerField51.installed]
    unfold ProverRwFullSampler.selected
    rw [ProverRwSamplerModel.sample_exact,hq]
    rfl
  · exact hcanonical
  · unfold PhaseSamplerParserBin.scalar R1J.SamplerLawSpend.s1Spend
    have same : R1J.SamplerLawSpend.arrEquiv b=PV_RunJoin_OpeningSampler50.block b := rfl
    rw [same,hq]
    rfl
#print axioms complete
end R1Z.PV_RunJoin_SemanticSampler51
