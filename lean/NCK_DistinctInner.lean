import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_DistinctInner
open Aeneas Aeneas.Std Result WP ControlFlow
open _root_.AdapterRw.r1_pool_adapter.owned
attribute [local instance] Classical.propDecidable
abbrev Accounts := Array OwnedAccount 7#usize

def key (a : Accounts) (j : Fin 7) : _root_.AdapterRw.solana_pubkey.Pubkey :=
  (a.val[j.val]'(by have := a.property; scalar_tac)).key

def Suffix (a : Accounts) (index : Fin 7) (start : Nat) : Prop :=
  ∀ j : Fin 7, start ≤ j.val → j.val < index.val → key a j ≠ key a index

def Comparison (ops : _root_.AdapterRw.Ops) : Prop :=
  ∀ x y, ops.op36 x y = ok (decide (x = y))

/-- Model induction for the exact inner distinct-account loop on seven
accounts. The primitive Pubkey equality law is explicit and not discharged. -/
theorem source (ops : _root_.AdapterRw.Ops) (a : Accounts) (index start : Usize)
    (within : index.val < 7) (ordered : start.val ≤ index.val)
    (comparison : Comparison ops) :
    require_distinct_accounts_loop0_loop0 ops a index start =
      ok (if Suffix a ⟨index.val,within⟩ start.val then none else
        some (.Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidArgument)) := by
  simp only [Comparison] at comparison
  have spec : require_distinct_accounts_loop0_loop0 ops a index start
      ⦃ out => out = if Suffix a ⟨index.val,within⟩ start.val then none else
        some (.Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidArgument) ⦄ := by
    unfold require_distinct_accounts_loop0_loop0
    refine loop.spec_decr_nat (fun j : Usize => index.val-j.val)
      (fun j : Usize => j.val ≤ index.val ∧
        (Suffix a ⟨index.val,within⟩ start.val ↔ Suffix a ⟨index.val,within⟩ j.val))
      (fun out => out = if Suffix a ⟨index.val,within⟩ start.val then none else
        some (.Err _root_.AdapterRw.solana_program_error.ProgramError.InvalidArgument))
      (fun j => require_distinct_accounts_loop0_loop0.body ops a index j)
      start ?_ ⟨ordered,Iff.rfl⟩
    intro j invariant
    rcases invariant with ⟨bound,equivalent⟩
    unfold require_distinct_accounts_loop0_loop0.body
    simp only [OwnedAccount.impl.key, comparison, bind_tc_ok]
    step*
    all_goals simp_all [Suffix,key]
    all_goals first | scalar_tac | skip
    · refine ⟨⟨j.val,by scalar_tac⟩,Nat.le_refl _,by scalar_tac,?_⟩
      assumption
    · have nowrap : (j.val+1) % Usize.size = j.val+1 := Nat.mod_eq_of_lt (by scalar_tac)
      rw [nowrap]
      refine ⟨by scalar_tac,?_,by scalar_tac⟩
      constructor
      · intro h k hk hi
        exact h k (by omega) hi
      · intro h k hk hi
        by_cases same : k.val = j.val
        · simpa only [same] using (show
            (a.val[j.val]'(by have := a.property; scalar_tac)).key ≠
            (a.val[index.val]'(by have := a.property; scalar_tac)).key from by assumption)
        · exact h k (by omega) hi
  obtain ⟨out,call,value⟩ := WP.spec_imp_exists spec
  rw [value] at call
  exact call
#print axioms source
end AspisR1.NCK_DistinctInner
end
