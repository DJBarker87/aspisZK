import NDO_JFo_Pending
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Flush
open Aeneas Aeneas.Std Result

/-- The installed mutable flush returns on every same-length64 pending
allocation; proving the actual query produced that allocation remains separate. -/
theorem source (b : AspisR1Stage2.verifier.BatchedWeights)
    (length : b.raw.val.length=64) :
    ∃ out, Port3_FlushInstall.flush b JFo_Prepared.accumulator.weights.deref=ok out ∧
      out.val.length=64 ∧ ∀ q∈out.val,Port3_FlushInstall.Canonical q := by
  have bound : JFo_Prepared.accumulator.weights.deref.val.length≤b.raw.val.length := by
    change JFo_Prepared.accumulator.weights.val.length≤b.raw.val.length
    rw [JFo_Prepared.weights_length,length]
  have run := Port3_FlushInstall.flush_exact b JFo_Prepared.accumulator.weights.deref bound
  refine ⟨_,run,?_,?_⟩
  · exact (Port3_FlushInstall.accepted_contents b _ _ bound run).2.trans JFo_Prepared.weights_length
  · exact Port3_FlushInstall.accepted_canonical b _ _ bound run

#print axioms source
end AspisR1.JFn_Flush
end
