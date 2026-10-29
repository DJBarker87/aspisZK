import R1Z.PV_RunJoin_CircleInstalled52
import R1Z.PV_RunJoin_CircleCoordinates55
import R1Z.PV_RunJoin_CircleCanonical55
import R1Z.PV_RunJoin_SemanticScalar50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleInstalledExact55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_CircleR72Carrier52
open ProverCommitSubfieldOps47

def coordinates (p : aspis_core.circle.SecureCirclePoint) :=
  (ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode (PV_RunJoin_SemanticScalar50.raw p.x)),
   ProverCommitValueRange47.embed (AspisR1.ExtractedCurrentQM31Exact.decode (PV_RunJoin_SemanticScalar50.raw p.y)))

theorem carrier (p : Point) : coordinates (PV_RunJoin_CircleNeutralSelected52.point p)=
    PV_RunJoin_CircleCoordinates55.coordinates p := rfl

theorem canonical (p : Point) (hx : PV_RunJoin_CircleNeutralShape53.QC p.1)
    (hy : PV_RunJoin_CircleNeutralShape53.QC p.2) :
    Canonical (PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_CircleNeutralSelected52.point p).x) ∧
    Canonical (PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_CircleNeutralSelected52.point p).y) :=
  ⟨hx,hy⟩

theorem source (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (b : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    @sampler.circle_sample (types base)
      (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops)) b row=
      ok (PV_RunJoin_CircleNeutralSelected52.point (decPoint
        (AspisV8R19.SamplerClosureCircleSourceExecution.encodePoint
          (AspisV8R19.SamplerCirclePolicy.point (PV_RunJoin_CircleTotal55.chosen b (PV_RunJoin_CircleNeutralSelected52.row row)))))) := by
  rw [PV_RunJoin_CircleInstalled52.complete,PV_RunJoin_CircleTotal55.complete,bind_tc_ok]

#print axioms coordinates
#print axioms carrier
#print axioms canonical
#print axioms source
end R1Z.PV_RunJoin_CircleInstalledExact55
