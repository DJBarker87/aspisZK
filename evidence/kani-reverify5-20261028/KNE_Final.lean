import KNE_Leaf
import KNE_Writer
set_option autoImplicit false
noncomputable section
namespace AspisR1.KNE_Final
open CheckpointBytes5Writer CheckpointBytes5Effect KNE_Caller KNE_Schedule

theorem schedule_facts (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (hp hu hc : Digest) :
    (derivedSchedule p a domain hp hu hc).length = 116 ∧
    ∀ s ∈ derivedSchedule p a domain hp hu hc, s.len+s.size ≤ s.cap := by
  simp only [derived_schedule]
  exact ⟨KND_Schedule.append_count,KND_Schedule.no_growth⟩

#print axioms KNE_Model.bodyEmissions_payload
#print axioms KNE_Model.bodyEmissions_shape
#print axioms KNE_Caller.every_reached_call
#print axioms KNE_Schedule.caller_final_len
#print axioms KNE_Schedule.derived_schedule
#print axioms KNE_Schedule.returned_decomposition
#print axioms KNE_Writer.cohort_program_eq
#print axioms KNE_Writer.emission_count
#print axioms KNE_Composition.compose
#print axioms KNE_Composition.body_bytes
#print axioms KNE_Leaf.native_result
#print axioms schedule_facts
end AspisR1.KNE_Final
end
