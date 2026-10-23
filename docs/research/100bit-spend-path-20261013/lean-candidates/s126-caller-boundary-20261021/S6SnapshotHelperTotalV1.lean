import S6SnapshotHelperSourceV1
import S6SourcePaymentCommonEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP ControlFlow
namespace AspisS6SnapshotHelper.Total
open AspisS6FiveUnrolledCodec
abbrev Snapshot := aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Range := core.ops.range.Range Usize
private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  change a.val.length=N.val
  exact a.property

@[step] theorem step_spec (snapshot : Snapshot) (output : Slice U8)
    (level : Usize) (hn : output.length=800) (hl : level.val<20) :
    frontier_step snapshot output level ⦃ result => result.length=800 ⦄ := by
  unfold frontier_step
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

/-- TOTAL caller-sized mutable frontier loop with actual length preservation. -/
theorem loop_total (iter : Range) (snapshot : Snapshot) (output : Slice U8)
    (he : iter.end.val=20) (hs : iter.start.val≤20) (hn : output.length=800) :
    ∃ out,frontier_loop_loop iter snapshot output=ok out ∧ out.length=800 := by
  have hw : frontier_loop_loop iter snapshot output ⦃ out => out.length=800 ⦄ := by
    unfold frontier_loop_loop
    refine loop.spec_decr_nat
      (fun s : Range × Slice U8 => 20-s.1.start.val)
      (fun s : Range × Slice U8 => s.1.end.val=20 ∧ s.1.start.val≤20 ∧ s.2.length=800)
      (fun out : Slice U8 => out.length=800)
      (fun s => frontier_loop_loop.body snapshot s.1 s.2) (iter,output) ?_ ⟨he,hs,hn⟩
    intro s h
    rcases s with ⟨range,buffer⟩
    rcases h with ⟨hend,hstart,hbuffer⟩
    unfold frontier_loop_loop.body
    step*
    all_goals (split at o_post1 <;> simp_all <;> scalar_tac)
  exact spec_imp_exists hw

theorem frontier_total (snapshot : Snapshot) (output : Slice U8) (hn : output.length=800) :
    ∃ out,frontier_loop snapshot output=ok out ∧ out.length=800 := by
  unfold frontier_loop
  exact loop_total _ snapshot output (by scalar_tac) (by scalar_tac) hn

#print axioms step_spec
#print axioms loop_total
#print axioms frontier_total
end AspisS6SnapshotHelper.Total
