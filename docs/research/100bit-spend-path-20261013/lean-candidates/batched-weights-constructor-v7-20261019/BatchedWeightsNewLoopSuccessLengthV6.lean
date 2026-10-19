import AspisR1BatchedWeightsExtraction.Funs
import BatchedWeightsNewLoopBodyLengthV18
import BatchedWeightsNewLoopBodyIterV6
import BatchedWeightsNewLoopBodyActiveV1
import OccupancyRangeTraversal
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
open BatchedWeightsNewLoopBodyLengthV18
open BatchedWeightsNewLoopBodyIterV6
open BatchedWeightsNewLoopBodyActiveV1
namespace BatchedWeightsNewLoopSuccessLengthV6
abbrev Raw := alloc.vec.Vec (Array Std.U64 4#usize)
abbrev Iter := core.ops.range.Range Std.Usize
def body (weights : Slice aspis_core.field.QM31) :
    (Iter × Raw) → Result (ControlFlow (Iter × Raw) Raw) :=
  fun s => batched_weights.BatchedWeights.new_loop.body weights s.1 s.2

theorem loop_success_cases {α β : Type} (step : α → Result (ControlFlow α β))
    (state : α) (out : β) (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hstep : step state with
  | fail e => simp [hstep] at h
  | div => simp [hstep] at h
  | ok cf =>
      cases cf with
      | done result =>
          simp [hstep] at h
          subst result
          exact Or.inl rfl
      | cont stateNext =>
          simp [hstep] at h
          exact Or.inr ⟨stateNext, rfl, h⟩

theorem loop_success_length_fuel
    (weights : Slice aspis_core.field.QM31) (iter : Iter) (raw : Raw)
    (fuel : Nat) (hspan : iter.start.val + fuel = iter.end.val)
    (out : Raw)
    (h : batched_weights.BatchedWeights.new_loop iter weights raw = .ok out) :
    out.length = raw.length := by
  change Aeneas.Std.loop (body weights) (iter, raw) = .ok out at h
  induction fuel generalizing iter raw out with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hcontFalse : ¬ ∃ s : Iter × Raw,
          (body weights) (iter, raw) = .ok (.cont s) := by
        rintro ⟨s, hc⟩
        have hactive := cont_implies_active weights iter raw s.1 s.2 (by simpa [body] using hc)
        omega
      rcases loop_success_cases (body weights) (iter, raw) out h with
        hdone | ⟨s, hcont, _⟩
      · have heq := done_success_raw weights iter raw out hdone
        simpa [heq]
      · exact False.elim (hcontFalse ⟨s, hcont⟩)
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      rcases loop_success_cases (body weights) (iter, raw) out h with
        hdone | ⟨s, hcont, htail⟩
      · have heq := done_success_raw weights iter raw out hdone
        simpa [heq]
      · rcases s with ⟨iterNext, rawNext⟩
        have hprogress := cont_success_iter weights iter raw iterNext rawNext hcont
        have hspanNext : iterNext.start.val + fuel = iterNext.end.val := by
          rcases hprogress with ⟨hstart, hend⟩
          rw [hstart, hend]
          omega
        have hnextLength : rawNext.length = raw.length :=
          cont_success_length weights iter raw iterNext rawNext hcont
        have hrec : Aeneas.Std.loop (body weights) (iterNext, rawNext) = .ok out := htail
        have hlen : out.length = rawNext.length := ih iterNext rawNext hspanNext out hrec
        exact hlen.trans hnextLength

#print axioms loop_success_length_fuel
end BatchedWeightsNewLoopSuccessLengthV6
