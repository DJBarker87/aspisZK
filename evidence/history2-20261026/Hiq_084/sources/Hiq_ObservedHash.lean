import Hiq_RecordedJoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_ObservedHash
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def hash (log : List (Bytes × State)) (input : Bytes) : State := by
  classical
  exact match log with
    | [] => fun _ => 0
    | head :: tail => if head.1 = input then head.2 else hash tail input

/-- The fallback is never used for any of the four charged input reads. -/
theorem consistent (H : Bytes → State) (log : List (Bytes × State)) (input : Bytes)
    (read : FS2.Duplex.Read log input) (answers : ∀ q ∈ log, q.2 = H q.1) : hash log input = H input := by
  classical
  induction log with
  | nil => simp [FS2.Duplex.Read] at read
  | cons head tail ih =>
    by_cases same : head.1 = input
    · simp only [hash,if_pos same]
      simpa only [same] using answers head (List.mem_cons_self _ _)
    · simp only [hash,if_neg same]
      apply ih
      · simpa only [FS2.Duplex.Read,List.map_cons,List.mem_cons,same,false_or] using read
      · intro q member
        exact answers q (List.mem_cons_of_mem _ member)

#print axioms consistent
end AspisR1.Hiq_ObservedHash
end
