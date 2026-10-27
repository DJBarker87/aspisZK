import XRk_ResultTools
open Aeneas Aeneas.Std Result ControlFlow
namespace XRk_LoopStep
theorem unroll {S V : Type} (body : S → Result (ControlFlow S V)) (s : S) (v : V)
    (run : loop body s = ok v) :
    ∃ step, body s = ok step ∧
      (match step with | .done out => ok out | .cont t => loop body t) = ok v := by
  rw [loop] at run
  cases h : body s with
  | fail e => simp only [h] at run; cases run
  | div => simp only [h] at run; cases run
  | ok step => exact ⟨step,rfl,by simpa only [h] using run⟩
#print axioms unroll
end XRk_LoopStep
