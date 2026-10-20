import FourDotsActualTermBodyLinearBoundV1
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace AspisR1FastDotsActualTermInputTraceRootV1
open AspisR1FastDotsActualTermBodyLinearBoundV1
abbrev U8 := Std.U8
abbrev U32 := Std.U32
abbrev U64 := Std.U64

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Exact actual arithmetic/slice/copy path supplying a term's four bytes.
These witnesses are derived from the source body, never supplied separately. -/
def TermBytesTrace (a : Array U8 608#usize) (slot term : Usize)
    (bytes : Array U8 4#usize) : Prop :=
  ∃ (o0 o1 o2 o3 o4 : Usize) (slice : Slice U8)
    (copied : core.result.Result (Array U8 4#usize) core.array.TryFromSliceError),
    (slot * 120#usize : Result Usize) = .ok o0 ∧ (term * 4#usize : Result Usize) = .ok o1 ∧
    (o0 + o1 : Result Usize) = .ok o2 ∧ (o0 + o1 : Result Usize) = .ok o3 ∧ (o3 + 4#usize : Result Usize) = .ok o4 ∧
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a {start := o2, «end» := o4} = .ok slice ∧
    core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 slice = .ok copied ∧
    core.result.Result.unwrap core.fmt.DebugTryFromSliceError copied = .ok bytes

/-- Successful actual term execution exposes the same term cursor, source
four-byte slice/copy, parser result, coefficient read and inner loop call. -/
theorem actual_term_body_success_input_trace
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hparser : ops.m31FromBytes = AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes)
    (hbody : TermBody ops a a1 slot iter sums = .ok (.cont (iter',sums'))) :
    ∃ (term : Usize) (bytes : Array U8 4#usize)
      (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
      (wide : Wide) (coeff : Array U32 8#usize),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some term,iter') ∧
      TermBytesTrace a slot term bytes ∧
      ops.m31FromBytes bytes = .ok (some scalar) ∧
      scalar.val < AspisR1DecodeKFullV10.aspis_core.field.P.val ∧
      Array.index_usize a1 term = .ok wide ∧ ops.wideToLimbs wide = .ok coeff ∧
      InnerLoop ops {start := 0#usize, «end» := 8#usize} sums scalar coeff = .ok sums'
 := by
  unfold TermBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some term =>
      obtain ⟨offset0, hslotMul, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨offset1, htermMul, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨offset2, hadd0, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨offset3, hadd1, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨offset4, hadd2, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨slice, hslice, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨copied, hcopy, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨bytes, hunwrapResult, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨parsed, hparse, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨scalar, hunwrapOption, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨wide, hwideRead, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨coeff, hcoeff, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨limbCount, hlimbCount, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨sumsFinal, hloop, hrest⟩ := bind_success _ _ _ hrest
      have hcont : (iter1, sumsFinal) = (iter', sums') :=
        ControlFlow.cont.inj (Result.ok.inj hrest)
      have hiter : iter1 = iter' := congrArg Prod.fst hcont
      have hsums : sumsFinal = sums' := congrArg Prod.snd hcont
      have hlimbCount' : limbCount = 8#usize :=
        Result.ok.inj (hlimbCount.symm.trans hcount)
      have hloop' : InnerLoop ops { start := 0#usize, «end» := 8#usize } sums scalar coeff = .ok sums' := by
        rw [hlimbCount'] at hloop
        simpa [hsums] using hloop
      have hparsedEq : parsed = some scalar := by
        cases parsed with
        | none => simp [core.option.Option.unwrap] at hunwrapOption
        | some value =>
            simp [core.option.Option.unwrap] at hunwrapOption
            subst scalar
            rfl
      have hscalar : scalar.val < AspisR1DecodeKFullV10.aspis_core.field.P.val := by
        have hparsed : AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes bytes =
            .ok (some scalar) := by
          simpa only [hparser, hparsedEq] using hparse
        exact AspisR1DecodeKFullV10ParserCanonicality.m31_from_le_bytes_success_canonical
          bytes scalar hparsed
      refine ⟨term,bytes,scalar,wide,coeff,?_,?_,?_,hscalar,hwideRead,hcoeff,hloop'⟩
      · simpa only [hiter] using hnext
      · exact ⟨offset0,offset1,offset2,offset3,offset4,slice,copied,
          hslotMul,htermMul,hadd0,hadd1,hadd2,hslice,hcopy,hunwrapResult⟩
      · simpa only [hparsedEq] using hparse

#print axioms actual_term_body_success_input_trace
end AspisR1FastDotsActualTermInputTraceRootV1
