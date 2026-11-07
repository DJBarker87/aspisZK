import NLW_ActualGetterScope
import NLW_StartScope
set_option autoImplicit false
noncomputable section
namespace NLW_ActualLength
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry
/-- The actual start call, actual getter and actual checked_add/guard derive
57607; no natural-sum premise or clone-dictionary substitution is supplied. -/
theorem length (ops : AdapterRw.Ops) (e : Entry) (bytes : Slice U8)
 (start end_ size : Usize)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
 (e.snapshot 0 58295 58295)=.ok (.Ok bytes))
 (startCall : AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops=.ok start)
 (checked : Usize.checked_add start size=some end_)
 (guard : (Slice.len bytes != end_)=false) : size.val=57607 := by
 rw [NLW_StartScope.proof_start ops] at startCall
 cases startCall
 have add := NLM_CheckedAddFacts.success 688#usize size end_ checked
 have eqLen := congrArg (fun n : Usize=>n.val) (NLM_CheckedAddFacts.guard_eq bytes end_ guard)
 rw [Slice.len_val] at eqLen
 have extent := NLW_ActualGetterScope.proof_extent ops e bytes read
 change end_.val=688+size.val at add
 have endExtent : end_.val=58295 := eqLen.symm.trans extent
 exact Nat.add_left_cancel (add.symm.trans endExtent)
#print length
#print axioms length
end NLW_ActualLength
