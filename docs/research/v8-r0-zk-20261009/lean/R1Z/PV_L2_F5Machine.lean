import R1Z.PV_L2_F5
import Query31ExplicitListLoop

/-! Operational recording of Q22, with a projection to the existing
source-shaped list-iterator loop. Native array IntoIter and std cost
refinement remain the same separate boundaries as in Query31. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F5Machine
open R1Z.PV_L2_F5 AspisV8R19.Q22WordScan
attribute [local instance] Classical.propDecidable

def execute : ScanState → List Nat → (ScanState × Bool) × List Event
  | s, [] => ((s,false),[.exhausted s])
  | s, x :: xs =>
    if hs : s.accepted.length = 22 ∨ s.draws = 64 then ((s,true),[.guard s true])
    else let rest := execute ⟨keep s.accepted x,s.draws+1⟩ xs
         (rest.1,.guard s false :: .candidate s.draws x (comparisons x s.accepted)
           (decide (x ∈ s.accepted)) :: rest.2)

theorem execute_erases (s : ScanState) (xs : List Nat) : (execute s xs).1 = scan s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [execute,scan]
    split_ifs
    · rfl
    · exact ih _

theorem execute_history (s : ScanState) (xs : List Nat) : (execute s xs).2 = scanHistory s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [execute,scanHistory]
    split_ifs
    · rfl
    · simp only [ih]

theorem comparisons_bounded (x : Nat) (xs : List Nat) : (comparisons x xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [comparisons,List.length_cons]
    split_ifs
    · simp only [List.length_nil]; omega
    · omega

theorem source_loop_record (xs : List Aeneas.Std.U32)
    (s : Query31ExplicitListLoop.CurrentScan)
    (valid : Query31ExplicitListLoop.validState s) :
    ∃ sf pending,
      Query31ExplicitListLoop.scanListLoop xs s = .ok (sf,pending) ∧
      (execute (Query31ExplicitScanBody.q22StateOf s) (xs.map (fun x => x.val))).1 =
        (Query31ExplicitScanBody.q22StateOf sf, Query31ExplicitListLoop.optionStop pending) := by
  obtain ⟨sf,pending,hs,hq⟩ := Query31ExplicitListLoop.scanListLoop_q22 xs s valid
  exact ⟨sf,pending,hs,(execute_erases _ _).trans hq⟩

#print axioms execute_erases
#print axioms execute_history
#print axioms comparisons_bounded
#print axioms source_loop_record
end R1Z.PV_L2_F5Machine
