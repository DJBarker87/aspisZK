import R1Z.ProverRw21ByteLengths
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21NodeLengths
open ProverRw21ProtocolOutput ProverCommitPublish43

theorem count : (List.ofFn slotNodes).sum=914 := by
  norm_num [List.ofFn_succ,slotNodes]

theorem capacities (t : Transcript) : ((slots t).map Slot.cap).sum=29248 := by
  simp only [ProverRw21ProtocolOutput.slots,List.map_ofFn]
  norm_num [List.ofFn_succ,slotNodes]

theorem slots_length (t : Transcript) (front result : Bytes)
    (success : ProverCommitPublish43.slots (slots t) front=.ok result) :
    result.length=front.length+29248 := by
  have h := ProverCommitPublish43.slots_length _ _ _ success
  rw [capacities] at h
  exact h

#print axioms count
#print axioms capacities
#print axioms slots_length
end R1Z.ProverRw21NodeLengths
