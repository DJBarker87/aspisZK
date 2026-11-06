import NLM_CheckedAddFacts
import NLM_ReadExtent
import NLM_EncoderExtent
import NLM_ScalarLaws
set_option autoImplicit false
noncomputable section
namespace NLW_StartScope
open Aeneas Aeneas.Std AspisR1.S2W_D189Entry
/-- The actual emitted start-constant call is8+680, with no Ops premise. -/
theorem proof_start (ops : AdapterRw.Ops) :
 AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops=.ok 688#usize := by
 unfold AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
 unfold AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
 have spec : (8#usize + 680#usize : Result Usize) ⦃z => z.val = 8+680⦄ := by
  apply UScalar.add_spec
  scalar_tac
 obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists spec
 have same : z=688#usize := by
  apply NLM_ScalarLaws.scalar_eq
  exact hval
 rw [same] at hz
 exact hz
/-- Every condition is a SAME entered source call/branch. No free58295 or
checked-natural equality supplies the proof_length result. -/
theorem actual_length (ops : AdapterRw.Ops) (e : Entry) (bytes : Slice U8)
 (start end_ length : Usize)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
  (e.snapshot 0 58295 58295)=.ok (.Ok bytes))
 (startCall : AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops=.ok start)
 (checked : Usize.checked_add start length=some end_)
 (guard : (Slice.len bytes != end_)=false) : length.val=57607 := by
 rw [proof_start ops] at startCall
 cases startCall
 exact NLM_CheckedAddFacts.proof_length ops e bytes end_ length read checked guard
/-- Obtain the whole resume scope from the actual owned getters, encoder
return carrier, start call, length-test arm and range return. This remains a
source/std clause until installed at the physical native parent cuts. -/
theorem actual_scope (ops : AdapterRw.Ops) (e : Entry)
 (bytes proof checkpoint : Slice U8) (publicBytes : Array U8 1880#usize)
 (statement : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1)
 (start end_ : Usize) (publicAddress proofAddress checkpointAddress : Nat)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
  (e.snapshot 0 58295 58295)=.ok (.Ok bytes))
 (checkpointRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
  (e.snapshot 6 1768 1768)=.ok (.Ok checkpoint))
 (_encoded : ops.op22 statement=.ok (.Ok publicBytes))
 (startCall : AdapterRw.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops=.ok start)
 (guard : (Slice.len bytes != end_)=false)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  bytes {start:=start,«end»:=end_}=.ok proof) :
 NLE_SafeCuts.Scope (NLE_CallerScope.metadata publicAddress proofAddress checkpointAddress
  publicBytes.to_slice proof checkpoint) := by
 rw [proof_start ops] at startCall
 cases startCall
 apply NLM_ReadExtent.scope ops e bytes proof checkpoint publicBytes end_ publicAddress proofAddress checkpointAddress read checkpointRead
 · have same := congrArg (fun n : Usize=>n.val) (NLM_CheckedAddFacts.guard_eq bytes end_ guard)
   simpa only [Slice.len_val] using same
 · exact range
#print proof_start
#print actual_length
#print actual_scope
#print axioms proof_start
#print axioms actual_length
#print axioms actual_scope
end NLW_StartScope
