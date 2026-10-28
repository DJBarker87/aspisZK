import NCK_DistinctInner
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_DistinctOuter
open Aeneas Aeneas.Std Result WP ControlFlow
open _root_.AdapterRw.r1_pool_adapter.owned NCK_DistinctInner
attribute [local instance] Classical.propDecidable

def Remaining (a : Accounts) (start : Nat) : Prop :=
  ∀ i j : Fin 7, start ≤ i.val → j.val < i.val → key a j ≠ key a i

/-- Model induction for the outer pair scan, retaining the SAME seven
accounts and the inner-loop equality law. Native step association is OPEN. -/
theorem source (ops : _root_.AdapterRw.Ops) (a : Accounts) (start : Usize)
    (ordered : start.val ≤ 7) (comparison : Comparison ops) :
    require_distinct_accounts_loop0 ops a start =
      ok (if Remaining a start.val then none else
        some (.Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidArgument)) := by
  have spec : require_distinct_accounts_loop0 ops a start
      ⦃ out => out = if Remaining a start.val then none else
        some (.Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidArgument) ⦄ := by
    unfold require_distinct_accounts_loop0
    refine loop.spec_decr_nat (fun i : Usize => 7-i.val)
      (fun i : Usize => i.val ≤ 7 ∧ (Remaining a start.val ↔ Remaining a i.val))
      (fun out => out = if Remaining a start.val then none else
        some (.Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidArgument))
      (fun i => require_distinct_accounts_loop0.body ops a i)
      start ?_ ⟨ordered,Iff.rfl⟩
    intro i invariant
    rcases invariant with ⟨bound,equivalent⟩
    unfold require_distinct_accounts_loop0.body
    by_cases running : i.val < 7
    · have active : i < 7#usize := by scalar_tac
      simp only [active,↓reduceIte,
        NCK_DistinctInner.source ops a i 0#usize running (by scalar_tac) comparison,
        bind_tc_ok]
      step*
      all_goals simp_all [Remaining,Suffix,key]
      all_goals first | scalar_tac | skip
    · step*
      all_goals simp_all [Remaining]
      all_goals first | scalar_tac | skip
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  rw [value] at call
  exact call

#print axioms source
end AspisR1.NCK_DistinctOuter
end
