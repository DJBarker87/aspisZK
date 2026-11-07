import NLW_ActualGetterScope
import NLW_StartScope
set_option autoImplicit false
noncomputable section
namespace NLW_ActualScope
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry
/-- No clone Ops replacement: all source scopes come from the SAME actual
returned getters, start call, comparison/range and encoder carrier. This is
still a local source cut clause, never a native root's successful-child premise. -/
theorem scope (ops : AdapterRw.Ops) (e : Entry)
 (account proof checkpoint : Slice U8) (publicBytes : Array U8 1880#usize)
 (start end_ : Usize) (pa pra ca : Nat)
 (readProof : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
 (e.snapshot 0 58295 58295)=.ok (.Ok account))
 (readCheckpoint : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
 (e.snapshot 6 1768 1768)=.ok (.Ok checkpoint))
 (startCall : AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops=.ok start)
 (guard : (Slice.len account != end_)=false)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
 account {start:=start,«end»:=end_}=.ok proof) :
 NLE_SafeCuts.Scope (NLE_CallerScope.metadata pa pra ca publicBytes.to_slice proof checkpoint) := by
 rw [NLW_StartScope.proof_start ops] at startCall
 cases startCall
 apply NLE_CallerScope.scope e account proof checkpoint publicBytes end_ pa pra ca
 · exact NLW_ActualGetterScope.stored ops e 0 58295 58295 account readProof
 · exact NLW_ActualGetterScope.stored ops e 6 1768 1768 checkpoint readCheckpoint
 · have same := congrArg (fun n : Usize=>n.val) (NLM_CheckedAddFacts.guard_eq account end_ guard)
   simpa only [Slice.len_val] using same
 · exact range
#print scope
#print axioms scope
end NLW_ActualScope
