import NDO_JFy_PreweightedGroup
import RPv_FIx_PreweightedLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PreweightedLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FIx_PreweightedLoop (R remaining)
open FIx_PreweightedLoopStep (loop)

theorem source {N : Usize} (r : R) (packed : Array field.QM31 24#usize)
    (start : Usize) (a : Array field.QM31 N) (he : r.end.val<24)
    (hp : canonical packed) (ha : canonical a) (bound : start.val+N.val≤96) :
    ∃ out,loop r packed start a=ok out ∧ canonical out := by
  generalize hcount : remaining r=count
  induction count using Nat.strong_induction_on generalizing r packed with
  | h count ih =>
    obtain ⟨⟨o,r'⟩,hn,post⟩ := WP.spec_imp_exists
      (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec r)
    by_cases empty : r.exhausted=true ∨ r.end.val<r.start.val
    · simp only [if_pos empty] at post
      obtain ⟨rfl,rfl⟩ := post
      refine ⟨packed,?_,hp⟩
      rw [FIx_PreweightedLoopStep.value,hn,bind_tc_ok]
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
      obtain ⟨next,hgroup,hnext⟩ := JFy_PreweightedGroup.source packed r.start start a hp ha (by omega) bound
      obtain ⟨out,tail,hout⟩ := ih (remaining r') decr r' next (by rw [he'];exact he) hnext rfl
      refine ⟨out,?_,hout⟩
      rw [FIx_PreweightedLoopStep.value,hn,bind_tc_ok]
      change (do let next ← FIx_PreweightedGroup.run packed r.start start a
                 loop r' next start a)=ok out
      rw [hgroup,bind_tc_ok,tail]
#print axioms source
end AspisR1.JFy_PreweightedLoop
end
