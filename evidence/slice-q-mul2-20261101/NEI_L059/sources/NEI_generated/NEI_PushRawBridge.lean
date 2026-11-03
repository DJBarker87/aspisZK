import NEI_PushRawAssociation
import NEI_VectorMeaning
import NEI_RowMemorySequence
set_option autoImplicit false
noncomputable section
namespace NEI_PushRawBridge
open Aeneas Aeneas.Std Result NEI_PushRawAssociation
/-- Same actual nominal emitted run, exact full carrier conversion, and the
unchanged terms/length frame. Success is derived from input safety only. -/
theorem complete (b : RawBW) (index : Usize) (p : RawPower) (basis : U32)
 (domain : NEI_PushBridge.Domain (toBW b) index (toPower p) basis) :
 ∃ out, NEI_PushRaw.BatchedWeights.push b index p basis=ok out ∧
 NEG_PushActual.BatchedWeights.push (toBW b) index (toPower p) basis=ok (toBW out) ∧
 (toBW out).terms=b.terms ∧ (toBW out).raw.val.length=b.raw.val.length := by
 obtain ⟨row,updated,read,safe,run,known⟩ := NEI_PushBridge.complete (toBW b) index (toPower p) basis domain
 have mapped := (NEI_PushRawAssociation.push b index p basis).trans known
 cases h : NEI_PushRaw.BatchedWeights.push b index p basis with
 | fail error => simp only [h,bind_tc_fail] at mapped; contradiction
 | div => simp only [h,bind_tc_div] at mapped; contradiction
 | ok out =>
  simp only [h,bind_tc_ok] at mapped
  have same := Result.ok.inj mapped
  refine ⟨out,rfl,?_,?_,?_⟩
  · rw [same];exact known
  · rw [same];rfl
  · rw [same]
    simp [toBW]
#print axioms complete
end NEI_PushRawBridge
end
