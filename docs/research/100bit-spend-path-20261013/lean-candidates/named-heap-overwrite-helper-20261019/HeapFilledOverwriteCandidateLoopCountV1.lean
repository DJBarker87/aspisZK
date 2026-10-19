import HeapFilledOverwriteCandidateLoopV1
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open HeapFilledOverwriteLoopV1
open AspisR1HeapFilledOverwrite
open HeapFilledOverwriteCandidateBodyV1

namespace HeapFilledOverwriteLoopCountV1

inductive SuccessfulTrace {α β : Type} (step : α → Result (ControlFlow α β)) :
    α → Nat → β → Prop where
  | done {state result} : step state = .ok (.done result) →
      SuccessfulTrace step state 0 result
  | cont {state next result count} :
      step state = .ok (.cont next) →
      SuccessfulTrace step next count result →
      SuccessfulTrace step state (count + 1) result

theorem filled_overwrite_loop_trace_count {T : Type} (value : T)
    (iter : HeapFilledOverwriteLoopV1.Iter) (raw : HeapFilledOverwriteLoopV1.Raw T) (fuel : Nat) (out : HeapFilledOverwriteLoopV1.Raw T)
    (hspan : iter.start.val + fuel = iter.end.val)
    (h : aspis_core.r0.heap.filled_overwrite_loop iter value raw = .ok out) :
    SuccessfulTrace (body value) (iter, raw) fuel out := by
  change Aeneas.Std.loop (body value) (iter, raw) = .ok out at h
  induction fuel generalizing iter raw out with
  | zero =>
      rcases loop_success_cases (body value) (iter, raw) out h with
        hdone | ⟨s, hcont, _⟩
      · exact SuccessfulTrace.done hdone
      · rcases s with ⟨iterNext, rawNext⟩
        have hactive := body_cont_active value iter raw iterNext rawNext hcont
        omega
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      rcases loop_success_cases (body value) (iter, raw) out h with
        hdone | ⟨s, hcont, htail⟩
      · exact False.elim (body_done_impossible value iter raw out hlt hdone)
      · rcases s with ⟨iterNext, rawNext⟩
        obtain ⟨hstart, hend, _⟩ := body_cont_update value iter raw iterNext rawNext hcont
        have hspanNext : iterNext.start.val + fuel = iterNext.end.val := by
          rw [hstart, hend]
          omega
        exact SuccessfulTrace.cont hcont (ih iterNext rawNext out hspanNext htail)

/-- With start zero and end `n`, a successful candidate loop makes exactly
`n` continuation transitions. Each transition is an actual `Vec.set` by
`HeapFilledOverwriteCandidateBodyV1.body_cont_update`. -/
theorem candidate_writes_exactly_n {T : Type} (value : T) (raw out : HeapFilledOverwriteLoopV1.Raw T)
    (n : Std.Usize)
    (h : aspis_core.r0.heap.filled_overwrite_loop { start := 0#usize, «end» := n }
      value raw = .ok out) :
    SuccessfulTrace (body value) ({ start := 0#usize, «end» := n }, raw)
      n.val out := by
  apply filled_overwrite_loop_trace_count value _ _ n.val out
  · simp
  · exact h

#print axioms filled_overwrite_loop_trace_count
#print axioms candidate_writes_exactly_n
end HeapFilledOverwriteLoopCountV1
