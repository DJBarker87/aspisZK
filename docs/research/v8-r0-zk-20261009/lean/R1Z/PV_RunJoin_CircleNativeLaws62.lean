import R1Z.PV_RunJoin_NativeResidual62
import R1Z.PV_RunJoin_CircleInstalledTotal55
import R1Z.PV_RunJoin_CircleUnit62
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleNativeLaws62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual62
open ProverCommitSubfieldOps47
attribute [local irreducible] R0P.SemSource.circleSample0 R0P.SemSource.circleSample1
  AspisV8R19.SqueezeOracleBridge.decodeState

theorem point_unit {K : Type} [Field K] (p : AspisR0.ChordGeometry.Point K) :
    p.val.1^2+p.val.2^2=1 := p.property


/-- Complete native-bound circle success and coordinate laws, all blocks and
both rows. CircleBinding62 records the inherited structural native boundary. -/
theorem complete (base : ExternalTypes) (heap : PV_RunJoin_WeightInstalled46.Heap)
    (box : PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base))
    (block : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    ∃ p,
      @sampler.circle_sample (types base) (opsNative base heap box ops) block row=ok p ∧
      Canonical (PV_RunJoin_SemanticScalar50.raw p.x) ∧
      Canonical (PV_RunJoin_SemanticScalar50.raw p.y) ∧
      (PV_RunJoin_CircleInstalledExact55.coordinates p).1^2+
        (PV_RunJoin_CircleInstalledExact55.coordinates p).2^2=1 := by
  obtain ⟨p,hp,hx,hy,hc⟩ := PV_RunJoin_CircleInstalledTotal55.complete
    (baseTypes base) heap box (beforeCircle base ops) block row
  refine ⟨p,hp,hx,hy,?_⟩
  rw [hc]
  split
  · exact PV_RunJoin_CircleUnit62.second block
  · exact PV_RunJoin_CircleUnit62.first block

#print axioms point_unit
#print axioms complete
end R1Z.PV_RunJoin_CircleNativeLaws62
