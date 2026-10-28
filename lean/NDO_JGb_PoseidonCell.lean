import NDO_JGb_Sum3
import NDO_JGb_PackSlice
import NDO_JFy_BoundedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_PoseidonCell
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)
open state_only_poseidon.evaluate_state_only_poseidon_oracle_projected

theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (internal : Array field.QM31 16#usize) (block : NP) (weights : Array NP 3#usize)
    (leading full : Array field.QM31 4#usize) (j : Usize) (hj : j.val<4)
    (hs : canonical o.succ_z) (hi : canonical internal) (hl : canonical leading) (hf : canonical full)
    (hb : JFy_PreparedSteps.Valid block) (hw : ∀ p∈weights.val,JFy_PreparedSteps.Valid p) :
    ∃ out,closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      (o,internal,block,weights,leading,full) j=ok (out,(o,internal,block,weights,leading,full)) ∧ Canon out := by
  obtain ⟨start,hstart,hsv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=4#usize) (y:=j) (by scalar_tac))
  obtain ⟨stop,hstop,hev⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=start) (y:=4#usize) (by scalar_tac))
  have len : start.val+4=stop.val := by scalar_tac
  have bound : stop.val≤16 := by scalar_tac
  obtain ⟨s0,hs0,len0,can0⟩ := JGb_PackSlice.source o.succ_z start stop len bound hs
  obtain ⟨s1,hs1,len1,can1⟩ := JGb_PackSlice.source internal start stop len bound hi
  obtain ⟨target,ht,htc⟩ := FIw_PackTotal.source s0 len0 can0
  obtain ⟨int,hit,hitc⟩ := FIw_PackTotal.source s1 len1 can1
  obtain ⟨l,hrl,lc⟩ := JFy_ArrayTotal.read leading j hj hl
  obtain ⟨f,hrf,fc⟩ := JFy_ArrayTotal.read full j hj hf
  obtain ⟨d0,hd0,c0,_⟩ := JFy_FieldTotal.sub target l htc lc
  obtain ⟨d1,hd1,c1,_⟩ := JFy_FieldTotal.sub target f htc fc
  obtain ⟨d2,hd2,c2,_⟩ := JFy_FieldTotal.sub target int htc hitc
  have cd : canonical (Array.make 3#usize [d0,d1,d2]) := by
    intro x hx
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  obtain ⟨sum,hsum,cs⟩ := JGb_Sum3.source weights _ hw cd
  obtain ⟨out,hout,co⟩ := WP.spec_imp_exists (JFy_PreparedSteps.mul block sum hb cs)
  refine ⟨out,?_,co⟩
  unfold closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  simp only [Aeneas.Std.uncurry]
  rw [hstart,bind_tc_ok,hstop,bind_tc_ok,hs0,bind_tc_ok,ht,bind_tc_ok,
    hs1,bind_tc_ok,hit,bind_tc_ok,hrl,bind_tc_ok,hd0,bind_tc_ok,hrf,bind_tc_ok,hd1,bind_tc_ok,
    hd2,bind_tc_ok,hsum,bind_tc_ok,hout,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGb_PoseidonCell
end
