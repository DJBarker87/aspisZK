import R1Z.PDict_TapeCells244
set_option autoImplicit false
namespace R1Z.PDict_TapeCorrect244
open Aeneas Aeneas.Std Result
open PDict_TapeView244

/-- Complete Result equality for the extracted owned tag-tape transition,
including mismatched requests, exhaustion, arbitrary values and OS error codes.
No entire-function equality or availability fact is supplied as a premise. -/
theorem reference_next (tape : Tape) (operation : U8) :
    (do let result ← PDict_TapeSource244.world.next tape operation
        .ok (result.reply,view result.tape)) = .ok (next operation (view tape)) := by
  by_cases small : tape.used.val < 16
  · obtain ⟨reply,read,position⟩ := source_index tape small
    have atIndex : (view tape).files[(view tape).fileUsed]? = some (event reply) := by
      change (view tape).files[tape.used.val]? = _
      rw [lookup,position]
      rfl
    by_cases same : reply.operation = operation
    · have model := PDict_EventWorld244.step_at (view tape) (event reply) atIndex
      have request : (event reply).request = operation := same
      rw [request] at model
      rw [PDict_TapeCells244.matched tape operation reply small read same]
      simp only [bind_tc_ok,next,model,event,advance tape small]
      rfl
    · have model := PDict_EventWorld244.mismatch (view tape) operation (event reply)
        atIndex same
      rw [PDict_TapeCells244.mismatched tape operation reply small read same]
      simp only [bind_tc_ok,next,model]
  · have large : 16 ≤ tape.used.val := by omega
    have position : (view tape).files[(view tape).fileUsed]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      change (view tape).files.length ≤ tape.used.val
      rw [capacity]
      exact large
    have model := PDict_EventWorld244.exhausted (view tape) operation position
    rw [PDict_TapeCells244.exhausted tape operation large]
    simp only [bind_tc_ok,next,model]

#print axioms reference_next
end R1Z.PDict_TapeCorrect244
