import S9ActualTensorSemanticCellV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualTensorInnerSemanticsV1
open AspisR1S9ActualTensorArithmeticV1 AspisR1S9TensorIndexedMeaningV1
open AspisR1S9TensorSemanticIndexV1 AspisR1S9ActualTensorWriteTraceV1
open AspisR1S9ActualTensorMarkedBodyV1 AspisR1S9ActualTensorInnerPrefixV1
open AspisR1S9MarkedSliceUpdateV1 AspisR1S9TensorIndexPartitionV2
open AspisR1S9ActualTensorSemanticCellV1 AspisR1S9LoopInvariantOutputV1
open AspisR1S9ReverseRangeProgressV1
abbrev Can := AspisR1S9ActualPairQMHelperTransportV1.Canonical
private def ReturnsCont {A B : Type} (m : Result (ControlFlow A B)) : Prop :=
  ∀ out, m = .ok out → ∃ state, out = .cont state

private theorem bind_returnsCont {A B C : Type} (m : Result A)
    (k : A → Result (ControlFlow B C)) (hk : ∀ x, ReturnsCont (k x)) :
    ReturnsCont (do let x ← m; k x) := by
  intro out h
  cases hm : m with
  | fail e => simp only [hm,bind_tc_fail] at h; cases h
  | div => simp only [hm,bind_tc_div] at h; cases h
  | ok x => simp only [hm,bind_tc_ok] at h; exact hk x out h

private theorem body_some_cont (self : weights.Weights) (k n d : Usize)
    (next : Iter) (input : Slice Q) (j : Usize) :
    ReturnsCont (B := weights.Weights × Slice Q) (do
    let x ← Slice.index_usize input j
    let a ← Array.index_usize self.factors k
    let a1 ← Array.index_usize a d
    let q ← Array.index_usize a1 0#usize
    let q1 ← aspis_core.field.QM31.mul x q
    let i ← lift (Std.Usize.wrapping_mul 0#usize n)
    let i1 ← lift (Std.Usize.wrapping_add j i)
    let input1 ← Slice.update input i1 q1
    let a2 ← Array.index_usize a d
    let q2 ← Array.index_usize a2 1#usize
    let q3 ← aspis_core.field.QM31.mul x q2
    let i2 ← lift (Std.Usize.wrapping_mul 1#usize n)
    let i3 ← lift (Std.Usize.wrapping_add j i2)
    let input2 ← Slice.update input1 i3 q3
    let a3 ← Array.index_usize a d
    let q4 ← Array.index_usize a3 2#usize
    let q5 ← aspis_core.field.QM31.mul x q4
    let i4 ← lift (Std.Usize.wrapping_mul 2#usize n)
    let i5 ← lift (Std.Usize.wrapping_add j i4)
    let input3 ← Slice.update input2 i5 q5
    let a4 ← Array.index_usize a d
    let q6 ← Array.index_usize a4 3#usize
    let q7 ← aspis_core.field.QM31.mul x q6
    let i6 ← lift (Std.Usize.wrapping_mul 3#usize n)
    let i7 ← lift (Std.Usize.wrapping_add j i6)
    let s ← Slice.update input3 i7 q7
    ok (cont (next, s))) := by
  repeat (apply bind_returnsCont; intro)
  intro out h
  exact ⟨_, (Result.ok.inj h).symm⟩

theorem source_body_done (self : weights.Weights) (k n d : Usize)
    (iter : Iter) (input : Slice Q) (out : weights.Weights × Slice Q)
    (h : weights.Weights.tensor_loop0_loop0.body self k n d iter input = .ok (.done out)) :
    out = (self,input) ∧ iter.iter.end.val ≤ iter.iter.start.val := by
  unfold weights.Weights.tensor_loop0_loop0.body at h
  cases hn : core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter with
  | fail e => simp only [hn,bind_tc_fail] at h; cases h
  | div => simp only [hn,bind_tc_div] at h; cases h
  | ok pair =>
    rcases pair with ⟨opt,next⟩
    cases opt with
    | none =>
      simp only [hn,bind_tc_ok] at h
      have ho := ControlFlow.done.inj (Result.ok.inj h)
      refine ⟨ho.symm,?_⟩
      by_contra hlt
      have hs := reverse_next_step iter (by omega)
      rw [hn] at hs
      cases hs
    | some j =>
      simp only [hn,bind_tc_ok] at h
      obtain ⟨state,heq⟩ := body_some_cont self k n d next input j (.done out) h
      cases heq


/-- The whole actual reverse-overwrite loop computes radix-four tensor
extension, using only an initialized input prefix. Scratch cells have no
semantic or canonicality premise. -/
theorem tensor_inner_semantics
    (base factor : Nat → ExactQM) (self : weights.Weights) (k n d : Usize)
    (iter : Iter) (input output : Slice Q) (selfOut : weights.Weights)
    (hn0 : 0<n.val) (hn : n.val≤16)
    (hs : iter.iter.start.val=0) (he : iter.iter.end=n)
    (hraw : MeaningOn decode base (fun i => i<n.val) input)
    (hcan : GoodOn Can (fun i => i<n.val) input)
    (hfactor : ∀ (row : Row) (coeffs : Array Q 4#usize) (t : Usize) (q : Q),
      Array.index_usize self.factors k = .ok row → Array.index_usize row d = .ok coeffs →
      Array.index_usize coeffs t = .ok q → Can q ∧ decode q = factor t.val)
    (hloop : weights.Weights.tensor_loop0_loop0 iter self k input n d = .ok (selfOut,output)) :
    selfOut=self ∧ MeaningOn decode (expanded base factor n.val) (fun i => i<4*n.val) output ∧
      GoodOn Can (fun i => i<4*n.val) output := by
  let step : (Iter × Slice Q) → Result (ControlFlow (Iter × Slice Q)
      (weights.Weights × Slice Q)) :=
    fun s => weights.Weights.tensor_loop0_loop0.body self k n d s.1 s.2
  let measure : (Iter × Slice Q) → Nat := fun s => s.1.iter.end.val
  let inv : (Iter × Slice Q) → Prop := fun s =>
    s.1.iter.start.val=0 ∧ s.1.iter.end.val≤n.val ∧
    GoodOn Can (Initialized n s.1) s.2 ∧
    MeaningOn decode base (fun i => i < s.1.iter.end.val) s.2 ∧
    MeaningOn decode (expanded base factor n.val) (Processed n.val s.1.iter.end.val) s.2
  let post : (weights.Weights × Slice Q) → Prop := fun r =>
    r.1=self ∧ MeaningOn decode (expanded base factor n.val) (fun i => i<4*n.val) r.2
  have hd : ∀ state result, inv state → step state = .ok (.done result) → post result := by
    rintro ⟨it,buf⟩ result hi hb
    dsimp only [inv] at hi
    rcases hi with ⟨hstart,hend,hgood,hbase,hproduct⟩
    obtain ⟨hout,hstop⟩ := source_body_done self k n d it buf result hb
    rw [hout]
    refine ⟨rfl,?_⟩
    apply meaning_mono decode (expanded base factor n.val) _ _ buf hproduct
    intro i hi
    exact ⟨hi,by omega⟩
  have hc : ∀ state next, inv state → step state = .ok (.cont next) →
      inv next ∧ measure next<measure state := by
    rintro ⟨it,buf⟩ ⟨itNext,bufNext⟩ hi hb
    dsimp only [inv] at hi
    rcases hi with ⟨hstart,hend,hgood,hbase,hproduct⟩
    obtain ⟨j,hj,hnextEnd,hrawNext,hproductNext⟩ :=
      tensor_body_semantic_progress base factor self k n d it itNext buf bufNext
        hn0 hn hend hbase hproduct hgood hfactor hb
    have hactive : ∀ jj next,
        core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
          (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) it =
            .ok (some jj,next) → Initialized n it jj.val := by
      intro jj next hjj
      obtain ⟨hjv,_,_⟩ := reverse_next_some_exact it next jj hjj
      exact Or.inl (by omega)
    obtain ⟨jj,hnext,hlen,hgoodNext⟩ := tensor_body_cont_marked_progress Can
      (Initialized n it) self k n d it itNext buf bufNext hgood hactive
      (fun row coeffs t q hr hc hq => (hfactor row coeffs t q hr hc hq).1)
      (fun a b c ha hb hm => (native_mul_success_exact a b c ha hb hm).1) hb
    obtain ⟨hjj,hendNext,hstartNext⟩ := reverse_next_some_exact it itNext jj hnext
    have heq : jj.val=j.val := by omega
    refine ⟨⟨?_,?_,?_,?_,?_⟩,?_⟩
    · simpa only [hstartNext] using hstart
    · dsimp only; omega
    · apply good_on_mono Can (fourMarks (Initialized n it) n jj) (Initialized n itNext) bufNext hgoodNext
      intro i hi
      apply initialized_next_covered n jj it.iter.end.val i hn0 hn hend hjj
      simpa only [Initialized,hendNext] using hi
    · simpa only [hnextEnd] using hrawNext
    · simpa only [hnextEnd] using hproductNext
    · dsimp only [measure]; omega
  have hi : inv (iter,input) := by
    refine ⟨hs,by change iter.iter.end.val≤n.val; rw [he],?_,?_,?_⟩
    · apply good_on_mono Can (fun i => i<n.val) (Initialized n iter) input hcan
      intro i hm
      rcases hm with hp|⟨_,hm⟩
      · exact hp
      · have hmod := Nat.mod_lt i hn0
        simp only [he] at hm
        omega
    · simpa only [he] using hraw
    · intro i q hr hm
      have hmod := Nat.mod_lt i.val hn0
      simp only [Processed,he] at hm
      omega
  have hl : Aeneas.Std.loop step (iter,input) = .ok (selfOut,output) := hloop
  obtain ⟨hself,hmeaning⟩ := loop_invariant_output step measure inv post hd hc (iter,input) (selfOut,output) hi hl
  have hcanOut := (tensor_inner_prefix Can self k n d iter input output selfOut hn0 hn hs he hcan
    (fun row coeffs t q hr hc hq => (hfactor row coeffs t q hr hc hq).1)
    (fun a b c ha hb hm => (native_mul_success_exact a b c ha hb hm).1) hloop).2
  exact ⟨hself,hmeaning,hcanOut⟩

#print axioms source_body_done
#print axioms tensor_inner_semantics
end AspisR1S9ActualTensorInnerSemanticsV1
