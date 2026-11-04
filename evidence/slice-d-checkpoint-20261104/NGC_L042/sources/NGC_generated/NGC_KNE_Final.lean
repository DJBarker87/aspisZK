import NGC_KNE_Leaf
import NGC_KNE_Writer
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_KNE_Final
open CheckpointBytes5Writer CheckpointBytes5Effect NGC_KNE_Caller NGC_KNE_Schedule

theorem schedule_facts (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (hp hu hc : Digest) :
    (derivedSchedule p a domain hp hu hc).length = 116 ∧
    ∀ s ∈ derivedSchedule p a domain hp hu hc, s.len+s.size ≤ s.cap := by
  simp only [derived_schedule]
  exact ⟨NGC_KND_Schedule.append_count,NGC_KND_Schedule.no_growth⟩

#print axioms NGC_KNE_Model.bodyEmissions_payload
#print axioms NGC_KNE_Model.bodyEmissions_shape
#print axioms NGC_KNE_Caller.every_reached_call
#print axioms NGC_KNE_Schedule.caller_final_len
#print axioms NGC_KNE_Schedule.derived_schedule
#print axioms NGC_KNE_Schedule.returned_decomposition
#print axioms NGC_KNE_Writer.cohort_program_eq
#print axioms NGC_KNE_Writer.emission_count
#print axioms NGC_KNE_Composition.compose
#print axioms NGC_KNE_Composition.body_bytes
#print axioms NGC_KNE_Leaf.native_result
#print axioms schedule_facts
end AspisR1.NGC_KNE_Final
end
