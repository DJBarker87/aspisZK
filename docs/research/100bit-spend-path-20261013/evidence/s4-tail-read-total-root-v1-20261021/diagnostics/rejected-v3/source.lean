import FourDotsActualTailBodyTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsTailReadTotalRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1

private theorem tryMk_small (n : Nat) (hn : n < 1024) :
    ∃ x : Usize, UScalar.tryMk UScalarTy.Usize n = .ok x ∧ x.val = n := by
  have hb : n < 2^UScalarTy.Usize.numBits := by
    have hbits : 32 ≤ UScalarTy.Usize.numBits := System.Platform.le_numBits
    have hp : 2^32 ≤ 2^UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by decide) hbits
    have hl : 1024 ≤ 2^32 := by decide
    omega
  have hb' : n < 2^System.Platform.numBits := hb
  let x : Usize := UScalar.ofNatCore n hb
  refine ⟨x, ?_, rfl⟩
  simp [UScalar.tryMk,UScalar.tryMkOpt,UScalar.check_bounds,hb',Result.ofOption,x]

private theorem mul_small (a b : Usize) (hn : a.val*b.val < 1024) :
    ∃ x : Usize, (a*b : Result Usize) = .ok x ∧ x.val=a.val*b.val := by
  change ∃ x : Usize, UScalar.tryMk UScalarTy.Usize (a.val*b.val) = .ok x ∧ _
  exact tryMk_small _ hn

private theorem add_small (a b : Usize) (hn : a.val+b.val < 1024) :
    ∃ x : Usize, (a+b : Result Usize) = .ok x ∧ x.val=a.val+b.val := by
  change ∃ x : Usize, UScalar.tryMk UScalarTy.Usize (a.val+b.val) = .ok x ∧ _
  exact tryMk_small _ hn

structure ReadWitness (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) where
  slot32 : Usize
  base480 : Usize
  term16 : Usize
  offset : Usize
  coeffIndex : Usize
  finish : Usize
  coefficient : Wide
  bytes : Slice Std.U8
  h0 : (slot*32#usize : Result Usize) = .ok slot32
  h1 : (480#usize+slot32 : Result Usize) = .ok base480
  h2 : (term*16#usize : Result Usize) = .ok term16
  h3 : (base480+term16 : Result Usize) = .ok offset
  h4 : (term+26#usize : Result Usize) = .ok coeffIndex
  hread : Array.index_usize g coeffIndex = .ok coefficient
  h5 : (offset+16#usize : Result Usize) = .ok finish
  hslice : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
    a {start:=offset, «end»:=finish} = .ok bytes
  coeff_value : coeffIndex.val=term.val+26
  offset_value : offset.val=480+slot.val*32+term.val*16
  finish_value : finish.val=480+slot.val*32+term.val*16+16
  bytes_value : bytes.val=a.val.slice offset.val finish.val
  bytes_length : bytes.length=16

/-- All checked arithmetic, coefficient reads and exact sixteen-byte slices
in the actual tail body succeed from the source slot/term bounds alone. -/
theorem tail_reads_total (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (hs : slot.val < 4) (ht : term.val < 2) :
    Nonempty (ReadWitness a g slot term) := by
  obtain ⟨slot32,h0,v0⟩ := mul_small slot 32#usize (by change slot.val*32<1024; omega)
  obtain ⟨base480,h1,v1⟩ := add_small 480#usize slot32 (by change 480+slot32.val<1024; omega)
  obtain ⟨term16,h2,v2⟩ := mul_small term 16#usize (by change term.val*16<1024; omega)
  obtain ⟨offset,h3,v3⟩ := add_small base480 term16 (by omega)
  obtain ⟨coeffIndex,h4,v4⟩ := add_small term 26#usize (by change term.val+26<1024; omega)
  have hi : coeffIndex.val < g.length := by
    have hh : coeffIndex.val < 29 := by change coeffIndex.val=term.val+26 at v4; omega
    simpa [Array.length,g.property] using hh
  obtain ⟨coefficient,hread,_⟩ := spec_imp_exists (Array.index_usize_spec g coeffIndex hi)
  obtain ⟨finish,h5,v5⟩ := add_small offset 16#usize (by change offset.val+16<1024; omega)
  have hb0 : offset ≤ finish := by change offset.val ≤ finish.val; change finish.val=offset.val+16 at v5; omega
  have hb1 : finish ≤ 608#usize := by
    change finish.val ≤ 608
    change slot32.val=slot.val*32 at v0
    change base480.val=480+slot32.val at v1
    change term16.val=term.val*16 at v2
    change finish.val=offset.val+16 at v5
    omega
  obtain ⟨bytes,hslice,hbytes,hlen⟩ := spec_imp_exists
    (Array.index_SliceIndexRangeUsizeSlice.step a {start:=offset, «end»:=finish} hb0 hb1)
  refine ⟨{
    slot32 := slot32
    base480 := base480
    term16 := term16
    offset := offset
    coeffIndex := coeffIndex
    finish := finish
    coefficient := coefficient
    bytes := bytes
    h0 := h0
    h1 := h1
    h2 := h2
    h3 := h3
    h4 := h4
    hread := hread
    h5 := h5
    hslice := hslice
    coeff_value := v4
    offset_value := ?_
    finish_value := ?_
    bytes_value := hbytes
    bytes_length := ?_ }⟩
  · change slot32.val=slot.val*32 at v0
    change base480.val=480+slot32.val at v1
    change term16.val=term.val*16 at v2
    omega
  · change slot32.val=slot.val*32 at v0
    change base480.val=480+slot32.val at v1
    change term16.val=term.val*16 at v2
    change finish.val=offset.val+16 at v5
    omega
  · change finish.val=offset.val+16 at v5
    omega

/-- Once the actual read prefix is installed, no additional arithmetic or
index hypothesis is needed for the parsed, accepted source push branch. -/
theorem actual_tail_body_from_reads
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (iter iter' : Range) (old next : Tail)
    (r : ReadWitness a g slot term) (q : QM)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some term,iter'))
    (hp : ops.qm31FromBytes r.bytes = .ok (some q))
    (hpush : ops.ebyKPush old r.coefficient q = .ok (.Ok (),next)) :
    TailBody ops a g slot iter old = .ok (.cont (iter',next)) := by
  simp only [TailBody,
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body,hn,r.h0,r.h1,r.h2,r.h3,r.h4,r.hread,r.h5,r.hslice,hp,hpush,
    core.option.Option.unwrap,core.result.Result.unwrap,bind_tc_ok]

#print axioms tail_reads_total
#print axioms actual_tail_body_from_reads
end AspisR1FastDotsTailReadTotalRootV1
