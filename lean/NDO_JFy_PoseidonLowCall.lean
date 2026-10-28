import RPv_JFy_ArrayTotal
import RPu_FIq_Native07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PoseidonLowCall
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open state_only_poseidon.evaluate_state_only_poseidon_oracle_projected

theorem full (s : state_only_poseidon.StateOnlyPoseidonSelectors) (acc : field.QM31) (i : Usize)
    (hs : canonical s.«local») (ha : Canon acc) (hi : i.val<16) :
    ∃ out,closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut s (acc,i)=ok (out,s) ∧ Canon out := by
  obtain ⟨q,hq,hqc⟩ := JFy_ArrayTotal.read s.«local» i hi hs
  obtain ⟨out,ho,hoc,_⟩ := FIv_PreparedTotal.add acc q ha hqc
  refine ⟨out,?_,hoc⟩
  unfold closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
  change (do let q ← Array.index_usize s.«local» i
             let out ← field.QM31.add acc q
             ok (out,s))=ok (out,s)
  rw [hq,bind_tc_ok,ho,bind_tc_ok]
#print axioms full

theorem internal (s : state_only_poseidon.StateOnlyPoseidonSelectors) (acc : field.QM31) (i : Usize)
    (hs : canonical s.«local») (ha : Canon acc) (hi : i.val<16) :
    ∃ out,closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut s (acc,i)=ok (out,s) ∧ Canon out := by
  exact full s acc i hs ha hi
#print axioms internal
end AspisR1.JFy_PoseidonLowCall
end
