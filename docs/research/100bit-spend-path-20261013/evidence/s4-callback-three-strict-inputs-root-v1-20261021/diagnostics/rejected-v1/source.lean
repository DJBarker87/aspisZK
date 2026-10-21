import FourDotsActualTailParserRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsActualCallbackParserRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailParserRootV1
open AspisR1FastDotsCurrentQmParserRootV1 (parser)

theorem indexed_sixteen_byte_frame {n : Usize} (a : Array Std.U8 n)
    (start finish : Usize) (bytes : Slice Std.U8)
    (hspan : finish.val=start.val+16)
    (hslice : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
      a {start, «end»:=finish}=.ok bytes) :
    bytes.val.length=16 ∧ bytes.val=a.val.slice start.val finish.val := by
  rw [Array.index_SliceIndexRangeUsizeSlice] at hslice
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hslice
  split at hslice
  · rename_i hb
    have heq := Result.ok.inj hslice
    have he := congrArg Subtype.val heq
    have hend : finish.val≤a.val.length := by
      simpa only [UScalar.le_equiv,Slice.length,Array.to_slice] using hb.2
    have hc : bytes.val=a.val.slice start.val finish.val := he.symm
    refine ⟨?_,hc⟩
    rw [hc,List.slice_length,hspan]
    have hdiff : start.val+16-start.val=16 := by omega
    rw [hdiff,Nat.min_eq_right (by omega)]
  · cases hslice

/-- The full emitted callback supplies all three strict QM31 tail inputs.
Its coefficient-28 input and the later coefficient-26/27 inputs are pinned
to the same original payload and actual accumulator run. -/
theorem actual_callback_success_three_strict_inputs
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (value : Wide) (closure' : Closure)
    (hbinding : ops.qm31FromBytes=parser)
    (hcall : Callback ops (a,g) slot=.ok (value,closure')) :
    closure'=(a,g) ∧
    ∃ (wide28 : Wide) (bytes : Slice Std.U8) (q : QM)
      (tail0 : Tail) (pushed : core.result.Result Unit Unit × Tail) (tail2 : Tail)
      (cs : List AspisR1FastDotsActualTailBodyTraceRootV1.Contribution),
      Array.index_usize g 28#usize=.ok wide28 ∧
      bytes.val=a.val.slice (slot.val*120+104) (slot.val*120+120) ∧
      StrictMeaning ⟨28#usize,wide28,bytes,q⟩ ∧
      ops.ebyKNew=.ok tail0 ∧ ops.ebyKPush tail0 wide28 q=.ok pushed ∧
      AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace ops a g slot
        {start:=0#usize, «end»:=2#usize} pushed.2 tail2 cs ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 ∧
      ∀ c ∈ cs, AspisR1FastDotsActualTailInputMeaningRootV1.SourceMeaning a g slot c ∧
        StrictMeaning c := by
  obtain ⟨hclosure,iter,limbs,vals,optBody,body,tail0,wide28,
    slotOffset,start,finish,bytes,optQ,q,pushed,u,tail2,tailValue,
    hstep,hbase,hvals,hbody,hunwrapBody,hnew,hread,hmul,hstart,hfinish,
    hslice,hparse,hunwrap,hpush,hunpush,hloop,hfinishTail,hadd⟩ :=
    actual_callback_success_base_and_tail ops a g slot value closure' hcall
  have vs : start.val=slotOffset.val+104 := by
    have h := UScalar.add_equiv slotOffset 104#usize
    rw [hstart] at h
    exact h.2.1
  have vf : finish.val=slotOffset.val+120 := by
    have h := UScalar.add_equiv slotOffset 120#usize
    rw [hfinish] at h
    exact h.2.1
  have vm : slotOffset.val=slot.val*120 := by
    have h := UScalar.mul_equiv slot 120#usize
    rw [hmul] at h
    exact h.2.1
  have hspan : finish.val=start.val+16 := by omega
  obtain ⟨hlen,hbytes⟩ := indexed_sixteen_byte_frame a start finish bytes hspan hslice
  have hstrict : StrictMeaning ⟨28#usize,wide28,bytes,q⟩ :=
    ⟨hlen,parser_slice_success ops bytes q optQ hlen hbinding hparse hunwrap⟩
  obtain ⟨cs,htrace,hi,hl,hmeanings⟩ :=
    actual_two_term_tail_success_strict ops a g slot pushed.2 tail2 hbinding hloop
  refine ⟨hclosure,wide28,bytes,q,tail0,pushed,tail2,cs,hread,?_,hstrict,hnew,hpush,
    htrace,hi,hl,hmeanings⟩
  simpa only [vs,vf,vm] using hbytes
#print axioms indexed_sixteen_byte_frame
#print axioms actual_callback_success_three_strict_inputs
end AspisR1FastDotsActualCallbackParserRootV1
