import StoredCarrierBindingObstruction
import StoredCarrierRawLayout
import StoredCarrierBindingComponents
import StoredCarrierPresentedHeadline

set_option autoImplicit false
namespace AspisR1.StoredCarrierFreeze
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortStoredExperimentC4 StoredCarrierPresentedModel

/-- A concrete satisfiable presentation for the logical runtime remainder. -/
theorem p2_self (hash : Bytes → State) (pub : Input → Bytes) :
    P2PrimeForInputs hash pub (written pub) := by
  intro i _
  exact ⟨rfl,rfl⟩
end AspisR1.StoredCarrierFreeze

#print axioms AspisR1.StoredCarrierFreeze.p2_self

/-! Focused union audit. This is not a frozen deployed-source closure replay. -/
#print axioms AspisR1.StoredCarrierBindingObstruction.same_bytes_insufficient
#print axioms AspisR1.StoredCarrierBindingObstruction.true_runtime_slots_insufficient
#print axioms AspisR1.StoredCarrierRawLayout.raw_length
#print axioms AspisR1.StoredCarrierRawLayout.raw_read
#print axioms AspisR1.StoredCarrierRawLayout.legacy_length_rejected
#print axioms AspisR1.StoredCarrierRawLayout.same_readers
#print axioms AspisR1.StoredCarrierRawLayout.staging_extensional
#print axioms AspisR1.StoredCarrierBindingComponents.run_ext
#print axioms AspisR1.StoredCarrierBindingComponents.binding_iff
#print axioms AspisR1.StoredCarrierPresentedModel.presented_same
#print axioms AspisR1.StoredCarrierPresentedModel.binding
#print axioms AspisR1.StoredCarrierPresentedHeadline.final_soundness
