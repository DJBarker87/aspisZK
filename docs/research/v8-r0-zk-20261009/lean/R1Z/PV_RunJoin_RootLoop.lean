import R1Z.PV_Src_Forest_BankRange
import R1Z.BuilderRecordsArray
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RootLoop
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open BuilderRecordsArray
variable [ExternalLinear]
abbrev Digest := Array U32 8#usize
abbrev Roots := Array Digest 21#usize

/-- The twenty-level source recurrence is discharged symbolically. The
remaining parent equations must be supplied by source permutation refinement;
no table hash or large concrete recurrence is normalized here. -/
theorem step (target roots : Roots)
    (parent : ∀ l : Fin 20,
      format.pool_v1_tree_parent target.val[l.val]! target.val[l.val]! =
        ok target.val[l.val+1]!)
    (iter after : core.ops.range.Range Usize)
    (hit : iter.start.val < 20)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      ok (some iter.start,after))
    (prior : Prefix roots target (iter.start.val+1)) :
    pair_trace.pair_empty_roots_loop iter roots =
      pair_trace.pair_empty_roots_loop after
        (roots.set (Usize.wrapping_add iter.start 1#usize)
          target.val[iter.start.val+1]!) := by
  rw [pair_trace.pair_empty_roots_loop,next]
  simp only [bind_tc_ok]
  rw [index_ok_gen roots iter.start (by simp;omega)]
  simp only [bind_tc_ok]
  rw [prior iter.start.val (by omega) (by simp;omega),parent ⟨iter.start.val,hit⟩]
  simp only [bind_tc_ok,lift]
  rw [update_gen _ _ _ (by rw [next_val iter.start (by omega)];simp;omega)]
  rfl

theorem loop (target : Roots)
    (parent : ∀ l : Fin 20,
      format.pool_v1_tree_parent target.val[l.val]! target.val[l.val]! =
        ok target.val[l.val+1]!)
    (iter : core.ops.range.Range Usize) (roots : Roots)
    (hend : iter.end = 20#usize) (hstart : iter.start.val ≤ 20)
    (prior : Prefix roots target (iter.start.val+1)) :
    pair_trace.pair_empty_roots_loop iter roots = ok target := by
  generalize he : 20-iter.start.val = remaining
  induction remaining using Nat.strong_induction_on generalizing iter roots with
  | h remaining ih =>
    by_cases hit : iter.start.val < 20
    · obtain ⟨after,hnext,hval,hafterend⟩ :=
        PV_Src_Forest_BankRange.next_some iter (by simpa [hend] using hit)
      rw [step target roots parent iter after hit hnext prior]
      have index_val := next_val iter.start (by omega)
      have value : target.val[iter.start.val+1]! =
          target.val[(Usize.wrapping_add iter.start 1#usize).val]! := by rw [index_val]
      rw [value]
      apply ih (20-after.start.val) (by omega) after _ (hafterend.trans hend) (by omega)
      · have pref : Prefix roots target (Usize.wrapping_add iter.start 1#usize).val := by
          simpa only [index_val] using prior
        simpa only [index_val,hval] using prefix_step roots target
          (Usize.wrapping_add iter.start 1#usize) (by rw [index_val];simp;omega) pref
      · rfl
    · rw [pair_trace.pair_empty_roots_loop,
        PV_Src_Forest_BankRange.next_none iter (by simpa [hend] using (show 20 ≤ iter.start.val by omega))]
      simp only [bind_tc_ok]
      have hv : iter.start.val+1 = (21#usize : Usize).val := by simp;omega
      rw [prefix_done roots target (by simpa only [hv] using prior)]

/-- Only the initial node and a uniform twenty-level parent law remain. The
loop, writes, indices and final table equality are ordinary source theorems. -/
theorem roots (target : Roots)
    (initial : format.pool_v1_tree_parent (Array.repeat 8#usize 0#u32)
      (Array.repeat 8#usize 0#u32) = ok target.val[0]!)
    (parent : ∀ l : Fin 20,
      format.pool_v1_tree_parent target.val[l.val]! target.val[l.val]! =
        ok target.val[l.val+1]!) :
    pair_trace.pair_empty_roots = ok target := by
  rw [pair_trace.pair_empty_roots,aspis_core.field.M31.ZERO,initial]
  simp only [bind_tc_ok]
  rw [update_gen _ 0#usize _ (by decide)]
  simp only [bind_tc_ok,format.POOL_V1_TREE_DEPTH,pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH]
  apply loop target parent _ _ rfl (by simp)
  intro j hj hn
  have hj0 : j = 0 := by simp at hj;omega
  subst j
  rw [BuilderRecordsArray.set_get _ _ _ _ (by decide),if_pos (show 0 = (0#usize : Usize).val by simp)]

#print axioms step
#print axioms loop
#print axioms roots
end R1Z.PV_RunJoin_RootLoop
