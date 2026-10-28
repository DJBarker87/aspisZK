import NDO_JFy_PoseidonLowCall
import RPv_FIx_PreweightedLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PoseidonInternalLow
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FIx_PreweightedLoop (R remaining)
open state_only_poseidon.evaluate_state_only_poseidon_oracle_projected

theorem loop (r : R) (s : state_only_poseidon.StateOnlyPoseidonSelectors) (acc : field.QM31)
    (he : r.end.val<16) (hs : canonical s.«local») (hc : Canon acc) :
    ∃ out,rangeFold core.iter.range.StepUsize closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31 r acc s=ok out ∧ Canon out := by
  generalize hcount : remaining r=count
  induction count using Nat.strong_induction_on generalizing r acc with
  | h count ih =>
    obtain ⟨⟨o,r'⟩,hn,post⟩ := WP.spec_imp_exists
      (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec r)
    by_cases empty : r.exhausted=true ∨ r.end.val<r.start.val
    · simp only [if_pos empty] at post
      obtain ⟨rfl,rfl⟩ := post
      refine ⟨acc,?_,hc⟩
      rw [rangeFold,hn,bind_tc_ok]
      rfl
    · have info : o=some r.start ∧ r'.end=r.end ∧ remaining r'<count := by
        by_cases more : r.start.val<r.end.val
        · simp only [if_neg empty,if_pos more] at post
          obtain ⟨ho,hs,he',hx⟩ := post
          refine ⟨ho,he',?_⟩
          rw [←hcount]
          unfold remaining
          simp only [if_neg empty,hx,Bool.false_eq_true,false_or,he']
          rw [if_neg (by omega)]
          omega
        · simp only [if_neg empty,if_neg more] at post
          obtain ⟨ho,hs,he',hx⟩ := post
          refine ⟨ho,he',?_⟩
          rw [←hcount]
          unfold remaining
          simp only [hx,true_or,↓reduceIte,if_neg empty]
          omega
      obtain ⟨rfl,he',decr⟩ := info
      obtain ⟨next,hgroup,hnext⟩ := JFy_PoseidonLowCall.internal s acc r.start hs hc (by omega)
      obtain ⟨out,tail,hout⟩ := ih (remaining r') decr r' next (by rw [he'];exact he) hnext rfl
      refine ⟨out,?_,hout⟩
      rw [rangeFold,hn,bind_tc_ok]
      change (do let (next,s') ← closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut s (acc,r.start)
                 rangeFold core.iter.range.StepUsize closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31 r' next s')=ok out
      rw [hgroup,bind_tc_ok]
      exact tail

#print axioms loop

theorem source (s : state_only_poseidon.StateOnlyPoseidonSelectors) (hs : canonical s.«local») :
    ∃ out,core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.fold core.iter.range.StepUsize
      closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31 ⟨2#usize,8#usize,false⟩ field.QM31.ZERO s=ok out ∧ Canon out :=
  loop _ s field.QM31.ZERO (by decide) hs FIv_NativeValue.zero.1
#print axioms source
end AspisR1.JFy_PoseidonInternalLow
end
