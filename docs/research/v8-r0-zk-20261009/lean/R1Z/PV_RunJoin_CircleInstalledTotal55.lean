import R1Z.PV_RunJoin_CircleInstalledExact55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleInstalledTotal55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_CircleR72Carrier52
open ProverCommitSubfieldOps47

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (b : Array U8 32#usize) (row : aspis_core.r0_transcript.CircleRow) :
    ∃ p,
    @sampler.circle_sample (types base)
      (selected base heap box (@PV_RunJoin_CircleNeutralSelected52.selected (types base) ops)) b row=ok p ∧
    Canonical (PV_RunJoin_SemanticScalar50.raw p.x) ∧ Canonical (PV_RunJoin_SemanticScalar50.raw p.y) ∧
    PV_RunJoin_CircleInstalledExact55.coordinates p=
      (if PV_RunJoin_CircleNeutralSelected52.row row then
        R0P.SemSource.circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState b)
       else R0P.SemSource.circleSample0 (AspisV8R19.SqueezeOracleBridge.decodeState b)).1 := by
  refine ⟨_,PV_RunJoin_CircleInstalledExact55.source base heap box ops b row,?_,?_,?_⟩
  · exact (PV_RunJoin_CircleInstalledExact55.canonical _ (PV_RunJoin_CircleCanonical55.encoded _).1 (PV_RunJoin_CircleCanonical55.encoded _).2).1
  · exact (PV_RunJoin_CircleInstalledExact55.canonical _ (PV_RunJoin_CircleCanonical55.encoded _).1 (PV_RunJoin_CircleCanonical55.encoded _).2).2
  · rw [PV_RunJoin_CircleInstalledExact55.carrier]
    exact PV_RunJoin_CircleCoordinates55.chosen b _
#print axioms complete
end R1Z.PV_RunJoin_CircleInstalledTotal55
