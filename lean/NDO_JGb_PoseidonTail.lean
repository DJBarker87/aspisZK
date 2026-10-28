import NDO_JGb_PoseidonCell
import NDO_JGb_PreparedMap
import NDO_JFy_PoseidonPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_PoseidonTail
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open state_only_poseidon.evaluate_state_only_poseidon_oracle_projected

/-- Complete native evaluator suffix after the three packed pair calls.
Their successful canonical outputs remain explicit and uninstantiated. -/
theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : state_only_poseidon.StateOnlyPoseidonSelectors)
    (leadingLow fullLow internalLow : field.QM31)
    (leading full : Array field.QM31 4#usize) (internal : Array field.QM31 16#usize)
    (hs : canonical o.succ_z) (hb : Canon s.block)
    (h0 : Canon leadingLow) (h1 : Canon fullLow) (h2 : Canon internalLow)
    (hl : state_only_poseidon.leading_pair_packed o=ok leading)
    (hf : state_only_poseidon.interpolated_full_pair_packed o.z s.local=ok full)
    (hi : state_only_poseidon.interpolated_internal_pair o.z s.local=ok internal)
    (cl : canonical leading) (cf : canonical full) (ci : canonical internal) :
    ∃ out,JFy_PoseidonPrefix.tail o s leadingLow fullLow internalLow=ok out ∧ canonical out := by
  have can : canonical (Array.make 3#usize [leadingLow,fullLow,internalLow]) := by
    intro x hx
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  obtain ⟨weights,hw,hwv⟩ := JGb_PreparedMap.source _ can
  obtain ⟨block,hbcall,hbv⟩ := WP.spec_imp_exists (JFy_PreparedSteps.new s.block hb)
  obtain ⟨out,hout,hoc⟩ : ∃ out,array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
      closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO
      (o,internal,block,weights,leading,full)=ok out ∧ canonical out := by
    unfold array_from_fn_copy
    apply JFy_BoundedCanonical.source
    intro j hj
    exact JGb_PoseidonCell.source o internal block weights leading full j hj hs ci cl cf hbv hwv
  refine ⟨out,?_,hoc⟩
  unfold JFy_PoseidonPrefix.tail
  rw [hl,bind_tc_ok,hf,bind_tc_ok,hi,bind_tc_ok,hw,bind_tc_ok,hbcall,bind_tc_ok,hout]
#print axioms source
end AspisR1.JGb_PoseidonTail
end
