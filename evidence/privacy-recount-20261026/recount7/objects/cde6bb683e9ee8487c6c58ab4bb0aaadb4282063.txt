import R1Z.PV_Src_RecordDynamic
import R1Z.BuilderBankRange
import R1Z.BuilderRecordsArray

/-! Symbolic complete-Result recurrence for the actual extracted empty-root
loop. Parent hashes stay opaque; no generated hash cell is reduced. -/
set_option autoImplicit false
namespace R1Z.PV_Src_RootRecurrence
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
abbrev Roots := BuilderRecordsReference.Roots

def step [ExternalLinear] (level : Usize) (roots : Roots) : Result Roots := do
  let a ← Array.index_usize roots level
  let parent ← format.pool_v1_tree_parent a a
  Array.update roots (Usize.wrapping_add level 1#usize) parent

def steps [ExternalLinear] (level : Usize) : Nat → Roots → Result Roots
  | 0, roots => ok roots
  | n+1, roots => do
      let after ← step level roots
      steps (Usize.wrapping_add level 1#usize) n after

theorem loop [ExternalLinear] (n : Nat) (iter : core.ops.range.Range Usize)
    (roots : Roots) (count : iter.start.val + n = iter.end.val)
    (bound : iter.end.val ≤ 20) :
    pair_trace.pair_empty_roots_loop iter roots = steps iter.start n roots := by
  induction n generalizing iter roots with
  | zero =>
    rw [pair_trace.pair_empty_roots_loop,BuilderBankRange.next_none iter (by omega)]
    rfl
  | succ n ih =>
    obtain ⟨after,hn,hs,he⟩ := BuilderBankRange.next_some iter (by omega)
    have ha : after.start = Usize.wrapping_add iter.start 1#usize := by
      apply UScalar.eq_of_val_eq
      rw [BuilderRecordsArray.next_val iter.start (by omega),hs]
    have hi : ∀ r : Roots, pair_trace.pair_empty_roots_loop after r =
        steps (Usize.wrapping_add iter.start 1#usize) n r := by
      intro r
      rw [← ha]
      exact ih after r (by rw [hs,he];omega) (by rw [he];exact bound)
    rw [pair_trace.pair_empty_roots_loop,hn]
    simp only [bind_tc_ok,steps,step,bind_assoc_eq,hi,lift]

#print axioms loop
end R1Z.PV_Src_RootRecurrence
