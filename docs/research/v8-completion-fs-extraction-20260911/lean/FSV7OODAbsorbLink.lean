import FSV7OODBodyScript
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7OODAbsorbLink
open FSOracleExecution FSExposureOrder FSTranscriptScript
open FSV7OODBodyScript FSV8OODBodyScript

abbrev Bytes := List UInt8
abbrev Point := FSV7OODBodyScript.Point
abbrev Tape := Nat → Block

theorem absorb_linked_after {A : Type} {m : Nat}
    (tape : Tape) (state : Block) (label : UInt8) (data : Bytes)
    (tail : Block → Script Bytes Block A m)
    (oracle : State Bytes Block) (answer : Block)
    (answer_eq : (query tape oracle (absorbInput state label data)).1 = answer) :
    LinkedAbsorb
      (run tape (FSTranscriptScript.bind (absorbScript state label data) tail) oracle).2.log
      (absorbInput state label data) answer := by
  obtain ⟨event, event_log, event_input, event_answer⟩ :=
    query_log tape oracle (absorbInput state label data)
  obtain ⟨suffix, suffix_eq⟩ :=
    run_extends tape (tail answer) (query tape oracle (absorbInput state label data)).2
  refine ⟨event, ?_, event_input, event_answer.trans answer_eq⟩
  have final_eq :
      (run tape (FSTranscriptScript.bind (absorbScript state label data) tail) oracle).2.log =
        (run tape (tail answer) (query tape oracle (absorbInput state label data)).2).2.log := by
    change
      (run tape (tail (query tape oracle (List.ofFn state ++ [0, label] ++ data)).1)
        (query tape oracle (List.ofFn state ++ [0, label] ++ data)).2).2.log =
        (run tape (tail answer)
          (query tape oracle (List.ofFn state ++ [0, label] ++ data)).2).2.log
    rw [show (query tape oracle (List.ofFn state ++ [0, label] ++ data)).1 = answer by
      exact answer_eq]
  rw [final_eq, suffix_eq]
  exact List.mem_append.mpr (Or.inl (by simpa [event_log]))

#print axioms absorb_linked_after

end AspisV8Completion.FSV7OODAbsorbLink
