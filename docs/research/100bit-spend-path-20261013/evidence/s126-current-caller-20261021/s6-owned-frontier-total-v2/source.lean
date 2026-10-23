import S6OwnedFrontierSourceV1
import S6SourcePaymentCommonEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP ControlFlow
namespace AspisS6OwnedFrontier.Total
open AspisS6FiveUnrolledCodec
abbrev Afterstate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev Range := core.ops.range.Range Usize

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  change a.val.length=N.val
  exact a.property

@[step] theorem step_spec (afterstate : Afterstate) (output : Array U8 688#usize)
    (level : Usize) (hl : level.val<20) :
    frontier_step afterstate output level ⦃ _ => True ⦄ := by
  unfold frontier_step
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

/-- TOTAL twenty-step reference by remaining-count induction, not unfolding
all twenty writes into one conversion term. -/
theorem loop_total (iter : Range) (afterstate : Afterstate) (output : Array U8 688#usize)
    (he : iter.end.val=20) (hs : iter.start.val≤20) :
    ∃ out,frontier_owned_loop iter afterstate output=ok out := by
  have hw : frontier_owned_loop iter afterstate output ⦃ _ => True ⦄ := by
    unfold frontier_owned_loop
    refine loop.spec_decr_nat
      (fun s : Range × Array U8 688#usize => 20-s.1.start.val)
      (fun s : Range × Array U8 688#usize => s.1.end.val=20 ∧ s.1.start.val≤20)
      (fun _ : Array U8 688#usize => True)
      (fun s => frontier_owned_loop.body afterstate s.1 s.2) (iter,output) ?_ ⟨he,hs⟩
    intro s h
    rcases s with ⟨range,buffer⟩
    rcases h with ⟨hend,hstart⟩
    unfold frontier_owned_loop.body
    step*
    all_goals (split at o_post1 <;> simp_all <;> scalar_tac)
  obtain ⟨out,h,_⟩ := spec_imp_exists hw
  exact ⟨out,h⟩

theorem frontier_total (afterstate : Afterstate) (output : Array U8 688#usize) :
    ∃ out,frontier_owned afterstate output=ok out := by
  unfold frontier_owned
  exact loop_total _ afterstate output (by scalar_tac) (by scalar_tac)

#print axioms step_spec
#print axioms loop_total
#print axioms frontier_total
end AspisS6OwnedFrontier.Total
