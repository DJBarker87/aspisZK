import FourDotsActualTailLoopTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTailInputMeaningRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1
open AspisR1FastDotsActualTailLoopTraceRootV1
abbrev U8 := Std.U8
abbrev Range := core.ops.range.Range Usize
private theorem tryMk_success_value {ty : UScalarTy} (n : Nat) (x : UScalar ty)
    (h : UScalar.tryMk ty n = .ok x) : x.val=n := by
  by_cases hb : n < 2^ty.numBits
  · let z : UScalar ty := UScalar.ofNatCore n hb
    have hz : UScalar.tryMk ty n = .ok z := by
      simp [UScalar.tryMk,UScalar.tryMkOpt,UScalar.check_bounds,hb,Result.ofOption,z]
    have hx : x=z := Result.ok.inj (h.symm.trans hz)
    rw [hx]
    rfl
  · simp [UScalar.tryMk,UScalar.tryMkOpt,UScalar.check_bounds,hb,Result.ofOption] at h

private theorem checked_mul_value (a b out : Usize)
    (h : (a*b : Result Usize) = .ok out) : out.val=a.val*b.val := by
  change UScalar.tryMk UScalarTy.Usize (a.val*b.val) = .ok out at h
  exact tryMk_success_value _ out h

private theorem checked_add_value (a b out : Usize)
    (h : (a+b : Result Usize) = .ok out) : out.val=a.val+b.val := by
  change UScalar.tryMk UScalarTy.Usize (a.val+b.val) = .ok out at h
  exact tryMk_success_value _ out h

private theorem actual_slice_contents
    (a : Array U8 608#usize) (start finish : Usize) (s : Slice U8)
    (hslice : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a {start, «end» := finish} = .ok s) :
    s.val=a.val.slice start.val finish.val := by
  rw [Array.index_SliceIndexRangeUsizeSlice] at hslice
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at hslice
  split at hslice
  · have heq := Result.ok.inj hslice
    exact (congrArg Subtype.val heq).symm
  · cases hslice

def SourceMeaning (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (c : Contribution) : Prop :=
  ∃ coeffIndex : Usize,
    coeffIndex.val=c.term.val+26 ∧ Array.index_usize g coeffIndex = .ok c.coefficient ∧
    c.bytes.val=a.val.slice (480+slot.val*32+c.term.val*16) (480+slot.val*32+c.term.val*16+16)

/-- The exact source coefficient and sixteen-byte input positions follow
from the same checked tail-body operations, without offset premises. -/
theorem input_witness_source_meaning
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (old next : Tail) (c : Contribution)
    (hw : InputWitness ops a g slot iter iter' old next c) : SourceMeaning a g slot c := by
  obtain ⟨slot32,base480,term16,offset,coeffIndex,finish,optQ,pushed,u,
    hnext,h0,h1,h2,h3,h4,hread,h5,hslice,hparse,hunwrap,hpush,hunpush,htail⟩ := hw
  have v0 : slot32.val=slot.val*32 := checked_mul_value slot 32#usize slot32 h0
  have v1 : base480.val=480+slot32.val := checked_add_value 480#usize slot32 base480 h1
  have v2 : term16.val=c.term.val*16 := checked_mul_value c.term 16#usize term16 h2
  have v3 : offset.val=base480.val+term16.val := checked_add_value base480 term16 offset h3
  have v4 : coeffIndex.val=c.term.val+26 := checked_add_value c.term 26#usize coeffIndex h4
  have v5 : finish.val=offset.val+16 := checked_add_value offset 16#usize finish h5
  have hb := actual_slice_contents a offset finish c.bytes hslice
  refine ⟨coeffIndex,v4,hread,?_⟩
  simpa only [v0,v1,v2,v3,v5] using hb

/-- The full same-state source tail trace retains each original input slice
and source coefficient position. -/
theorem actual_tail_trace_source_meanings
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (old out : Tail) (cs : List Contribution)
    (htrace : RunTrace ops a g slot iter old out cs) :
    ∀ c ∈ cs, SourceMeaning a g slot c := by
  induction htrace with
  | done iter old hbody => intro c hc; cases hc
  | step c cs hbody hwitness htail ih =>
      intro x hx
      rcases List.mem_cons.mp hx with heq | htailmem
      · subst x
        exact input_witness_source_meaning ops a g slot _ _ _ _ c hwitness
      · exact ih x htailmem
#print axioms input_witness_source_meaning
#print axioms actual_tail_trace_source_meanings
end AspisR1FastDotsActualTailInputMeaningRootV1
