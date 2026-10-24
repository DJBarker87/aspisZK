import S9ActualTensorArithmeticV1
import S9TensorIndexedMeaningV1
import S9TensorSemanticIndexV1
import S9ActualTensorInnerPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualTensorSemanticCellV1
open AspisR1S9ActualTensorArithmeticV1 AspisR1S9TensorIndexedMeaningV1
open AspisR1S9TensorSemanticIndexV1 AspisR1S9ActualTensorWriteTraceV1
open AspisR1S9ActualTensorMarkedBodyV1 AspisR1S9ActualTensorInnerPrefixV1
open AspisR1S9MarkedSliceUpdateV1 AspisR1S9TensorIndexPartitionV2
abbrev Can := AspisR1S9ActualPairQMHelperTransportV1.Canonical

def expanded (base factor : Nat → ExactQM) (n i : Nat) : ExactQM :=
  base (i%n) * factor (i/n)

/-- Source semantics for one reverse tensor iteration. Unread input entries
retain their old meaning and processed output entries have the radix-four
product meaning. Input scratch outside those two sets is unconstrained. -/
theorem tensor_body_semantic_progress
    (base factor : Nat → ExactQM) (self : weights.Weights) (k n d : Usize)
    (iter iterOut : Iter) (input output : Slice Q)
    (hn0 : 0<n.val) (hn : n.val≤16) (hrem : iter.iter.end.val≤n.val)
    (hraw : MeaningOn decode base (fun i => i<iter.iter.end.val) input)
    (hprod : MeaningOn decode (expanded base factor n.val)
      (Processed n.val iter.iter.end.val) input)
    (hcan : GoodOn Can (Initialized n iter) input)
    (hfactor : ∀ (row : Row) (coeffs : Array Q 4#usize) (t : Usize) (q : Q),
      Array.index_usize self.factors k = .ok row → Array.index_usize row d = .ok coeffs →
      Array.index_usize coeffs t = .ok q → Can q ∧ decode q = factor t.val)
    (hbody : weights.Weights.tensor_loop0_loop0.body self k n d iter input =
      .ok (.cont (iterOut,output))) :
    ∃ j, j.val+1=iter.iter.end.val ∧ iterOut.iter.end.val=j.val ∧
      MeaningOn decode base (fun i => i<j.val) output ∧
      MeaningOn decode (expanded base factor n.val) (Processed n.val j.val) output := by
  obtain ⟨j,x,row,coeffs,q0,q1,q2,q3,y0,y1,y2,y3,s1,s2,s3,
    hnext,hread,hrow,hcoeffs,hq0,hy0,hs1,hq1,hy1,hs2,hq2,hy2,hs3,hq3,hy3,hs4⟩ :=
    tensor_body_cont_write_trace self k n d iter iterOut input output hbody
  obtain ⟨hj,hend,_⟩ := reverse_next_some_exact iter iterOut j hnext
  have hjn : j.val<n.val := by omega
  have hx : Can x := hcan j x hread (Or.inl hjn)
  have hb : decode x=base j.val := hraw j x hread (by omega)
  have f0 := hfactor row coeffs 0#usize q0 hrow hcoeffs hq0
  have f1 := hfactor row coeffs 1#usize q1 hrow hcoeffs hq1
  have f2 := hfactor row coeffs 2#usize q2 hrow hcoeffs hq2
  have f3 := hfactor row coeffs 3#usize q3 hrow hcoeffs hq3
  have m0 := (native_mul_success_exact x q0 y0 hx f0.1 hy0).2
  have m1 := (native_mul_success_exact x q1 y1 hx f1.1 hy1).2
  have m2 := (native_mul_success_exact x q2 y2 hx f2.1 hy2).2
  have m3 := (native_mul_success_exact x q3 y3 hx f3.1 hy3).2
  have idx (t : Usize) (ht : t.val≤3) :
      (writeIndex n j t).val=j.val+t.val*n.val :=
    (tensor_index_val n j t hn hjn ht).1
  have val (t : Usize) (ht : t.val≤3) (q y : Q)
      (hf : decode q=factor t.val) (hm : decode y=decode x*decode q) :
      decode y=expanded base factor n.val (writeIndex n j t).val := by
    obtain ⟨hmod,hdiv⟩ := tensor_write_mod_div n j t hn hjn ht
    change (writeIndex n j t).val % n.val=j.val at hmod
    change (writeIndex n j t).val / n.val=t.val at hdiv
    rw [expanded,hmod,hdiv,hm,hb,hf]
  have p0 := val 0#usize (by simp) q0 y0 f0.2 m0
  have p1 := val 1#usize (by simp) q1 y1 f1.2 m1
  have p2 := val 2#usize (by simp) q2 y2 f2.2 m2
  have p3 := val 3#usize (by simp) q3 y3 f3.2 m3
  have cover (mark : Nat → Prop) (t : Usize) :
      ∀ i, addMark mark (writeIndex n j t) i →
        i=(writeIndex n j t).val ∨ mark i := by intro i hi; exact hi
  have hp0 := update_meaning_on decode _ _ _ input s1 _ y0 hprod p0 (cover _ _) hs1
  have hp1 := update_meaning_on decode _ _ _ s1 s2 _ y1 hp0 p1 (cover _ _) hs2
  have hp2 := update_meaning_on decode _ _ _ s2 s3 _ y2 hp1 p2 (cover _ _) hs3
  have hp3 := update_meaning_on decode _ _ _ s3 output _ y3 hp2 p3 (cover _ _) hs4
  have hraw0 : MeaningOn decode base (fun i => i<j.val) input :=
    meaning_mono decode base _ _ input hraw (by intro i hi; omega)
  have away (t : Usize) (ht : t.val≤3) :
      ∀ i, i<j.val → i≠(writeIndex n j t).val := by
    intro i hi heq
    have htidx := idx t ht
    omega
  have hr0 := update_meaning_frame decode base _ input s1 _ y0 hraw0 (away _ (by simp)) hs1
  have hr1 := update_meaning_frame decode base _ s1 s2 _ y1 hr0 (away _ (by simp)) hs2
  have hr2 := update_meaning_frame decode base _ s2 s3 _ y2 hr1 (away _ (by simp)) hs3
  have hr3 := update_meaning_frame decode base _ s3 output _ y3 hr2 (away _ (by simp)) hs4
  refine ⟨j,hj,hend,hr3,?_⟩
  apply meaning_mono decode (expanded base factor n.val) _ _ output hp3
  intro i hi
  have hc := processed_step_covered n.val iter.iter.end.val j.val i hn0 hj hi
  unfold addMark
  rcases hc with ho|h0|h1|h2|h3
  · exact Or.inr (Or.inr (Or.inr (Or.inr ho)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [idx 0#usize (by simp)] using h0))))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [idx 1#usize (by simp)] using h1)))
  · exact Or.inr (Or.inl (by simpa only [idx 2#usize (by simp)] using h2))
  · exact Or.inl (by simpa only [idx 3#usize (by simp)] using h3)

#print axioms tensor_body_semantic_progress
end AspisR1S9ActualTensorSemanticCellV1
