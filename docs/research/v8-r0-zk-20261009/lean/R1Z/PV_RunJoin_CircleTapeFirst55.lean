import R1Z.PV_RunJoin_CircleInstalledTotal55
import R1Z.PV_RunJoin_OpeningByteCodec51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleTapeFirst55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem model (b : R0Z.FsStatement.OracleAnswer) :
    (PhaseSamplerParserBin.circle ⟨0,by decide⟩ b).1=
      (R0P.SemSource.circleSample0 (AspisV8R19.SqueezeOracleBridge.decodeState (PV_RunJoin_OpeningSampler50.block b))).1 := by
  change (R0P.SemSource.circleSample0 (fun i => (b i).toFin)).1=_
  unfold PV_RunJoin_OpeningSampler50.block
  rw [AspisV8R19.SqueezeOracleBridge.state_roundtrip]
  rfl

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (b : R0Z.FsStatement.OracleAnswer) :
    ∃ q,
      @sampler.circle_sample (types base)
        (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops))
        (PV_RunJoin_OpeningSampler50.block b) .First=ok q ∧
      ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw q.x) ∧
      ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw q.y) ∧
      PV_RunJoin_CircleInstalledExact55.coordinates q=(PhaseSamplerParserBin.circle ⟨0,by decide⟩ b).1 := by
  obtain ⟨q,hq,hx,hy,hm⟩ := PV_RunJoin_CircleInstalledTotal55.complete base heap box ops (PV_RunJoin_OpeningSampler50.block b) .First
  refine ⟨q,hq,hx,hy,?_⟩
  rw [model]
  exact hm
#print axioms model
#print axioms complete
end R1Z.PV_RunJoin_CircleTapeFirst55
