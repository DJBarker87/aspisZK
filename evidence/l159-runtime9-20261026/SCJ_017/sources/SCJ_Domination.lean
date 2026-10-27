import SCJ_Projection
import SCI_Recovery
import SCF_Domination
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Domination
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open RawRecordedOracleExtractionMassBin OraclePortRefineJoin
attribute [local instance] Classical.propDecidable

/-- Full-log charge alone cannot pay even the indicator of the projected
release event on arbitrary consistent sublists. Not a deployed forgery. -/
theorem indicator_obstruction (Q : Nat) :
    ∃ (small full : List (Bytes × State)), small.Sublist full ∧
      indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) (small,())) >
      indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) (full,())) := by
  obtain ⟨small,full,sub,clean,hit⟩ := SCJ_Projection.clean_transport_refuted Q
  refine ⟨small,full,sub,?_⟩
  simp only [indicator,if_pos hit,if_neg clean]
  norm_num

/-- Exact composition consumer: the needed implication is visible, rather
than being silently replaced by sublist containment. No unconditional
physical account instance is claimed. -/
theorem of_transport (left right : RawCutProverCompiler.RunView)
    (projected full : Prop)
    (transport : projected → full)
    (branch : left.2.2 = true → ¬ projected →
      right.2.2 = true ∧ RecoveredInputAgreement left right) :
    failureMass left ≤ failureMass right + indicator full := by
  apply SCF_Domination.pointwise_of_agreement left right full
  intro accepted clean
  exact branch accepted (fun hit => clean (transport hit))

#print axioms indicator_obstruction
#print axioms of_transport
end AspisR1.SCJ_Domination
end
