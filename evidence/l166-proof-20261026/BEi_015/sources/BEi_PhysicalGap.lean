import BEi_RecorderCut
set_option autoImplicit false
namespace AspisR1.BEi_PhysicalGap
open Aeneas Aeneas.Std Result SdkC_Source

/-- A fixed erased result and complete final carrier do not determine a
physical attempted history. This holds for EVERY actual computed outcome,
including any outcome selected by the current deployed theorem. It is an
interface non-implication, not a counterexample to the shipped machine. -/
theorem extension {S A E : Type} (out : BEh_Scope.Outcome S A E) (query : Query) :
    let extra : BEh_Scope.Outcome S A E := (out.1,out.2.1,out.2.2 ++ [query])
    extra.1 = out.1 ∧ extra.2.1 = out.2.1 ∧
    extra.2.2.length = out.2.2.length + 1 ∧ ¬ BEh_Scope.Law extra out := by
  refine ⟨rfl,rfl,?_,?_⟩
  · exact List.length_append ..
  · intro law
    have logs := BEh_Scope.logs _ _ law
    have lengths := congrArg List.length logs
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

/-- Even a full unrelated native/game/security proposition remains compatible
with both recorder decorations when its statement has no such argument.
No inconsistency in the retained trust/game hypotheses is used. -/
theorem retained_facts {S A E : Type} (out : BEh_Scope.Outcome S A E)
    (query : Query) (Facts : Prop) (facts : Facts) :
    Facts ∧ ∃ other : BEh_Scope.Outcome S A E,
      other.1 = out.1 ∧ other.2.1 = out.2.1 ∧ ¬ BEh_Scope.Law other out := by
  have example := extension out query
  exact ⟨facts,⟨(out.1,out.2.1,out.2.2 ++ [query]),example.1,example.2.1,example.2.2.2⟩⟩

/-- Operational association actually rules out the extra recorder attempt.
This pinpoints the missing proof rather than assuming observation equality. -/
theorem operational_excludes_extension {S A E : Type}
    (call : Parts → S → Result Digest × S) (code : Code (core.result.Result A E))
    (state after : S) (before log : Log) (value : Result (core.result.Result A E))
    (execution : BEi_Execution.Executes call code state before value after log) (query : Query) :
    ¬ BEi_Execution.Executes call code state before value after (log ++ [query]) := by
  intro other
  have same := (BEi_ExecutionUnique.unique call code state after after before log (log ++ [query])
    value value execution other).2.2
  have lengths := congrArg List.length same
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega

#print axioms extension
#print axioms retained_facts
#print axioms operational_excludes_extension
end AspisR1.BEi_PhysicalGap
