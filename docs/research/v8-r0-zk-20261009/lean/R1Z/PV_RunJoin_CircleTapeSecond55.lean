import R1Z.PV_RunJoin_CircleInstalledTotal55
import R1Z.PV_RunJoin_CircleSelector55
import R1Z.PV_RunJoin_CircleTapeState55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleTapeSecond55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem model (b : R0Z.FsStatement.OracleAnswer) :
    (PhaseSamplerParserBin.circle ⟨1,by decide⟩ b).1=
      (R0P.SemSource.circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState (PV_RunJoin_OpeningSampler50.block b))).1 := by
  rw [PV_RunJoin_CircleSelector55.second,PV_RunJoin_CircleTapeState55.decode]
  rfl

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (b : R0Z.FsStatement.OracleAnswer) :
    ∃ q,
      @sampler.circle_sample (types base)
        (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops))
        (PV_RunJoin_OpeningSampler50.block b) .Second=ok q ∧
      ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw q.x) ∧
      ProverCommitSubfieldOps47.Canonical (PV_RunJoin_SemanticScalar50.raw q.y) ∧
      PV_RunJoin_CircleInstalledExact55.coordinates q=(PhaseSamplerParserBin.circle ⟨1,by decide⟩ b).1 := by
  obtain ⟨q,hq,hx,hy,hm⟩ := PV_RunJoin_CircleInstalledTotal55.complete base heap box ops (PV_RunJoin_OpeningSampler50.block b) .Second
  refine ⟨q,hq,hx,hy,?_⟩
  rw [model]
  simpa only [PV_RunJoin_CircleNeutralSelected52.row,if_true] using hm
#print axioms model
#print axioms complete
end R1Z.PV_RunJoin_CircleTapeSecond55
