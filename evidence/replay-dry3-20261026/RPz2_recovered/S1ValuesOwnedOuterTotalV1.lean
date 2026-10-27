import S1ValuesOwnedOuterStepTotalV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedTotal
open Aeneas Aeneas.Std Result WP ControlFlow AspisS1ValuesOwned

/-- TOTAL actual outer loop by decreasing remaining chunk count. -/
theorem outer_loop_total (input output : Buffer) (count chunk : Usize)
    (inputRange : count.val*16 ≤ input.length)
    (outputRange : count.val*32 ≤ output.length) :
    ∃ next updated, values_owned_reference_loop input output count chunk=ok (next,updated) := by
  have aux : ∀ n (input output : Buffer) (chunk : Usize), count.val-chunk.val=n →
      count.val*16 ≤ input.length → count.val*32 ≤ output.length →
      ∃ next updated, values_owned_reference_loop input output count chunk=ok (next,updated) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro input output chunk measure hi ho
      by_cases active : chunk.val<count.val
      · obtain ⟨next,updated,chunk1,step,sameInput,sameLength,advance⟩ :=
          outer_step_total input output count chunk active hi ho
        have smaller : count.val-chunk1.val<n := by omega
        have hi1 : count.val*16 ≤ next.length := by rw [sameInput];exact hi
        have ho1 : count.val*32 ≤ updated.length := by rw [sameLength];exact ho
        obtain ⟨finalInput,finalOutput,tail⟩ :=
          ih (count.val-chunk1.val) smaller next updated chunk1 rfl hi1 ho1
        refine ⟨finalInput,finalOutput,?_⟩
        unfold values_owned_reference_loop at tail ⊢
        unfold loop
        dsimp only
        rw [step]
        exact tail
      · refine ⟨input,output,?_⟩
        have test : ¬chunk<count := by scalar_tac
        unfold values_owned_reference_loop
        unfold loop
        simp only [values_owned_reference_loop.body,if_neg test]
  exact aux (count.val-chunk.val) input output chunk rfl inputRange outputRange


@[step] theorem outer_spec (input output : Buffer) (count chunk : Usize)
    (inputRange : count.val*16 ≤ input.length)
    (outputRange : count.val*32 ≤ output.length) :
    values_owned_reference_loop input output count chunk ⦃ _ => True ⦄ := by
  obtain ⟨next,updated,call⟩ := outer_loop_total input output count chunk inputRange outputRange
  rw [call]
  trivial

#print axioms outer_loop_total
#print axioms outer_spec
end AspisS1ValuesOwnedTotal
