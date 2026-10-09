import FSV8AlphaRootLabeledTraceConstructor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 220000

namespace AspisV8Completion.FSV8AlphaLabeledPrefixDecomposition
open AspisK1.V7Tag73CausalSlotMachineRouter
open FSV8AlphaRootLabeledTraceConstructor
noncomputable section
universe u

theorem machine_labeled_answers_append
    {Output Slot : Type} {State : Type u}
    (machine : PreAnswerSlotMachine Output Slot State)
    (state : State) (first second : List Output) :
    machineLabeledAnswers machine state (first ++ second) =
      machineLabeledAnswers machine state first ++
        machineLabeledAnswers machine
          (machineStateAfterAnswers machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons answer rest ih =>
      simp only [List.cons_append, machineLabeledAnswers,
        machineStateAfterAnswers]
      rw [ih]

theorem machine_labeled_answers_at_cut
    {Output Slot : Type} {State : Type u}
    (machine : PreAnswerSlotMachine Output Slot State)
    (state : State) (before after : List Output) (answer : Output) :
    machineLabeledAnswers machine state (before ++ answer :: after) =
      machineLabeledAnswers machine state before ++
        (machine.preferredSlot
          (machineStateAfterAnswers machine state before), answer) ::
        machineLabeledAnswers machine
          (machine.afterAnswer
            (machineStateAfterAnswers machine state before) answer) after := by
  rw [machine_labeled_answers_append]
  rfl

theorem machine_labeled_answers_prefix
    {Output Slot : Type} {State : Type u}
    (machine : PreAnswerSlotMachine Output Slot State)
    (state : State) (before after : List Output) :
    machineLabeledAnswers machine state before <+:
      machineLabeledAnswers machine state (before ++ after) := by
  rw [machine_labeled_answers_append]
  exact List.prefix_append _ _

#print axioms machine_labeled_answers_append
#print axioms machine_labeled_answers_at_cut
#print axioms machine_labeled_answers_prefix
end
end AspisV8Completion.FSV8AlphaLabeledPrefixDecomposition
