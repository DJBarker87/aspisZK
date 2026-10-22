import S4HeadLoopForwardRootV1
import S4FirstTailReadTotalRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsHeadReadForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops M31)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (InnerLoop Range)
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev TermBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body
open AspisR1FastDotsFirstTailReadTotalRootV1 (small_checked_mul small_checked_add)

structure ReadWitness (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) where
  base : Usize
  delta : Usize
  start : Usize
  finish : Usize
  bytes : Slice Std.U8
  copied : Array Std.U8 4#usize
  coefficient : Wide
  hmulSlot : (slot*120#usize : Result Usize) = .ok base
  hmulTerm : (term*4#usize : Result Usize) = .ok delta
  hadd : (base+delta : Result Usize) = .ok start
  hfinish : (start+4#usize : Result Usize) = .ok finish
  hslice : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
    a {start:=start,«end»:=finish} = .ok bytes
  hcopy : core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 bytes =
    .ok (.Ok copied)
  hread : Array.index_usize g term = .ok coefficient
  start_value : start.val=slot.val*120+term.val*4
  finish_value : finish.val=slot.val*120+term.val*4+4
  bytes_value : bytes.val=a.val.slice start.val finish.val
  copied_value : copied.val=bytes.val

theorem head_reads_total (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (hs : slot.val<4) (ht : term.val<26) :
    Nonempty (ReadWitness a g slot term) := by
  obtain ⟨base,hm0,hv0⟩ := small_checked_mul slot 120#usize (by change slot.val*120<1024; omega)
  change base.val=slot.val*120 at hv0
  obtain ⟨delta,hm1,hv1⟩ := small_checked_mul term 4#usize (by change term.val*4<1024; omega)
  change delta.val=term.val*4 at hv1
  obtain ⟨start,ha,hva⟩ := small_checked_add base delta (by omega)
  obtain ⟨finish,hf,hvf⟩ := small_checked_add start 4#usize (by change start.val+4<1024; omega)
  change finish.val=start.val+4 at hvf
  have hb0 : start ≤ finish := by change start.val≤finish.val; omega
  have hb1 : finish ≤ 608#usize := by change finish.val≤608; omega
  obtain ⟨bytes,hsl,hbv,hbl⟩ := WP.spec_imp_exists
    (Array.index_SliceIndexRangeUsizeSlice.step a {start:=start,«end»:=finish} hb0 hb1)
  have hlen : bytes.length=4 := by change bytes.length=finish.val-start.val at hbl; omega
  obtain ⟨copiedResult,hcopy,hpost⟩ := WP.spec_imp_exists
    (core.array.TryFromArrayCopySlice.try_from.step 4#usize core.marker.CopyU8 bytes)
  cases copiedResult with
  | Err e =>
    cases e
    have hn : bytes.length≠(4#usize).val := hpost
    exact False.elim (hn (by simpa using hlen))
  | Ok copied =>
    obtain ⟨coefficient,hr,_⟩ := WP.spec_imp_exists
      (Array.index_usize_spec g term (by simpa [Array.length,g.property] using (show term.val<29 by omega)))
    exact ⟨{
      base := base
      delta := delta
      start := start
      finish := finish
      bytes := bytes
      copied := copied
      coefficient := coefficient
      hmulSlot := hm0
      hmulTerm := hm1
      hadd := ha
      hfinish := hf
      hslice := hsl
      hcopy := hcopy
      hread := hr
      start_value := by omega
      finish_value := by omega
      bytes_value := hbv
      copied_value := hpost.1 }⟩

theorem term_body_from_reads
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (iter iter' : Range) (sums out : Array Std.U64 8#usize)
    (r : ReadWitness a g slot term) (scalar : M31) (coefficient : Array Std.U32 8#usize)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some term,iter'))
    (hp : ops.m31FromBytes r.copied = .ok (some scalar))
    (hw : ops.wideToLimbs r.coefficient = .ok coefficient)
    (hc : ops.wideLimbCount = .ok 8#usize)
    (hl : InnerLoop ops {start:=0#usize,«end»:=8#usize} sums scalar coefficient = .ok out) :
    TermBody ops a g slot iter sums = .ok (.cont (iter',out)) := by
  have hsl := r.hslice
  rw [Array.index_SliceIndexRangeUsizeSlice] at hsl
  simp [TermBody,
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body,
    hn,r.hmulSlot,r.hmulTerm,r.hadd,r.hfinish,hsl,r.hcopy,r.hread,hp,hw,hc,hl,
    core.result.Result.unwrap,core.option.Option.unwrap]

#print axioms head_reads_total
#print axioms term_body_from_reads
end AspisR1FastDotsHeadReadForwardRootV1
