import AspisV8R19.R445InitialBlockRejectionLaw

set_option autoImplicit false
namespace AspisV8R19.R446RejectionListExecution
open R442RejectionAlphabet R443BoundedRejectionMass

theorem run_list {p : Nat} (n : Nat) (t : Tape p n) :
    run n t = firstAccepted (List.ofFn t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      cases h : t 0 with
      | none => simpa [run, firstAccepted, h] using ih (fun i => t i.succ)
      | some a => simp [run, firstAccepted, h]

/-- The source sentinel branch, before any masking or memory reads. -/
def sentinelScan (p : Nat) : List Nat → Option Nat
  | [] => none
  | w :: ws => if w = p then sentinelScan p ws else some w

theorem decode_value {p : Nat} (w : Fin (p+1)) :
    Option.map Fin.val (alphabetDecode p w) =
      if w.val = p then none else some w.val := by
  by_cases h : w.val < p
  · have hn : w.val ≠ p := by omega
    simp [alphabetDecode, h, hn]
  · have he : w.val = p := by omega
    simp [alphabetDecode, h, he]

theorem sentinel_list {p : Nat} (ws : List (Fin (p+1))) :
    sentinelScan p (ws.map Fin.val) =
      Option.map Fin.val (firstAccepted (ws.map (alphabetDecode p))) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      by_cases h : w.val < p
      · have hn : w.val ≠ p := by omega
        simp [sentinelScan, alphabetDecode, h, hn, firstAccepted]
      · have he : w.val = p := by omega
        simpa [sentinelScan, alphabetDecode, h, he, firstAccepted] using ih

#print axioms run_list
#print axioms decode_value
#print axioms sentinel_list
end AspisV8R19.R446RejectionListExecution
