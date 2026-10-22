import S4TailReadTotalRootV1
import S4HeadTailSharedWitnessRootV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsFirstTailReadTotalRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1

/-- Reuse the checked-Usize library semantics with a small symbolic bound. -/
theorem small_checked_mul (a b : Usize) (h : a.val*b.val < 1024) :
    ∃ x : Usize, (a*b : Result Usize) = .ok x ∧ x.val=a.val*b.val := by
  have hm : a.val*b.val ≤ Usize.max := by
    have hh : 1024 ≤ Usize.max := by scalar_tac
    omega
  have hs : (a*b : Result Usize) ⦃x => x.val=a.val*b.val⦄ := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq] using hm
  exact WP.spec_imp_exists hs

theorem small_checked_add (a b : Usize) (h : a.val+b.val < 1024) :
    ∃ x : Usize, (a+b : Result Usize) = .ok x ∧ x.val=a.val+b.val := by
  have hm : a.val+b.val ≤ Usize.max := by
    have hh : 1024 ≤ Usize.max := by scalar_tac
    omega
  have hs : (a+b : Result Usize) ⦃x => x.val=a.val+b.val⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hm
  exact WP.spec_imp_exists hs

structure FirstReadWitness (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) where
  offset : Usize
  start : Usize
  finish : Usize
  bytes : Slice Std.U8
  coefficient : Wide
  hmul : (slot*120#usize : Result Usize) = .ok offset
  hstart : (offset+104#usize : Result Usize) = .ok start
  hfinish : (offset+120#usize : Result Usize) = .ok finish
  hslice : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
    a {start:=start, «end»:=finish} = .ok bytes
  hcoefficient : Array.index_usize g 28#usize = .ok coefficient
  offset_value : offset.val=slot.val*120
  start_value : start.val=slot.val*120+104
  finish_value : finish.val=slot.val*120+120
  bytes_value : bytes.val=a.val.slice start.val finish.val
  bytes_length : bytes.length=16

/-- The initial QM tail scalar and g[28] read always exist on every source
slot, independently of bytes, coefficient canonicality or parser acceptance. -/
theorem first_tail_reads_total (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (hs : slot.val < 4) : Nonempty (FirstReadWitness a g slot) := by
  obtain ⟨offset,hmul,vo⟩ := small_checked_mul slot 120#usize (by change slot.val*120<1024; omega)
  change offset.val=slot.val*120 at vo
  obtain ⟨start,hstart,vs⟩ := small_checked_add offset 104#usize (by change offset.val+104<1024; omega)
  change start.val=offset.val+104 at vs
  obtain ⟨finish,hfinish,vf⟩ := small_checked_add offset 120#usize (by change offset.val+120<1024; omega)
  change finish.val=offset.val+120 at vf
  have hb0 : start ≤ finish := by change start.val≤finish.val; omega
  have hb1 : finish ≤ 608#usize := by change finish.val≤608; omega
  obtain ⟨bytes,hslice,hbytes,hlen⟩ := WP.spec_imp_exists
    (Array.index_SliceIndexRangeUsizeSlice.step a {start:=start,«end»:=finish} hb0 hb1)
  have hi : (28#usize).val < g.length := by simp [Array.length,g.property]
  obtain ⟨coefficient,hcoefficient,_⟩ := WP.spec_imp_exists (Array.index_usize_spec g 28#usize hi)
  refine ⟨{
    offset := offset
    start := start
    finish := finish
    bytes := bytes
    coefficient := coefficient
    hmul := hmul
    hstart := hstart
    hfinish := hfinish
    hslice := hslice
    hcoefficient := hcoefficient
    offset_value := vo
    start_value := by omega
    finish_value := by omega
    bytes_value := hbytes
    bytes_length := ?_ }⟩
  change bytes.length=finish.val-start.val at hlen
  omega

/-- Installs exactly the checked first-query input used by the same callback;
only the strict parser acceptance remains a premise. -/
theorem first_query_input_of_reads (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (r : FirstReadWitness a g slot) (q : QM)
    (hparse : ops.qm31FromBytes r.bytes = .ok (some q)) :
    AspisR1FastDotsHeadTailSharedWitnessRootV2.FirstQueryInput ops a slot q :=
  ⟨r.offset,r.start,r.finish,r.bytes,r.hmul,r.hstart,r.hfinish,r.hslice,hparse⟩

/-- All three tail input prefixes are forward total for each of the four
source slots; this is not a claim about parser or dot-kernel execution. -/
theorem all_tail_reads_total (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (hs : slot.val < 4) :
    Nonempty (FirstReadWitness a g slot ×
      AspisR1FastDotsTailReadTotalRootV1.ReadWitness a g slot 0#usize ×
      AspisR1FastDotsTailReadTotalRootV1.ReadWitness a g slot 1#usize) := by
  obtain ⟨r⟩ := first_tail_reads_total a g slot hs
  obtain ⟨r0⟩ := AspisR1FastDotsTailReadTotalRootV1.tail_reads_total a g slot 0#usize hs (by decide)
  obtain ⟨r1⟩ := AspisR1FastDotsTailReadTotalRootV1.tail_reads_total a g slot 1#usize hs (by decide)
  exact ⟨r,r0,r1⟩

#print axioms small_checked_mul
#print axioms small_checked_add
#print axioms first_tail_reads_total
#print axioms first_query_input_of_reads
#print axioms all_tail_reads_total
end AspisR1FastDotsFirstTailReadTotalRootV1
