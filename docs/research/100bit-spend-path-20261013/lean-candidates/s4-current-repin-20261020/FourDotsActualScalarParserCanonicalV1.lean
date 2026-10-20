import AspisR1FastDotsCurrent.FunsOpsV4
import AspisR1FastDotsCurrentM31OpsBinding

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualScalarParserCanonical

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev M31 := AspisR1FastDotsCurrent.aspis_core.field.M31
abbrev Range := core.ops.range.Range Usize
abbrev BatchBody :=
  AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful exact emitted outer term body exposes the actual four-byte
    M31 decode used as its scalar, and the retained source parser proves that
    successful decoded scalar is canonical. Iterator, slice-read, coefficient
    lookup and reducer behavior remain independently bounded by their callers. -/
theorem body_success_scalar_canonical
    (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : BatchBody (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer ops)
      a a1 slot iter sums = .ok (.cont (iter', sums'))) :
    ∃ term : Usize, ∃ bytes : Array U8 4#usize, ∃ scalar : M31,
      (AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer ops).m31FromBytes bytes =
        .ok (some scalar) ∧ scalar.val < AspisR1DecodeKFullV10.aspis_core.field.P.val := by
  unfold BatchBody at hbody
  obtain ⟨result, hnext, hrest⟩ := bind_success _ _ _ hbody
  rcases result with ⟨term?, iter1⟩
  cases term? with
  | none => cases hrest
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
    cases parsed with
    | none =>
      simp [core.option.Option.unwrap] at hunwrapOption
    | some value =>
      simp [core.option.Option.unwrap] at hunwrapOption
      subst scalar
      exact ⟨term, bytes, value, hparse,
        AspisR1FastDotsCurrentM31OpsBinding.parser_success_canonical
          ops bytes value hparse⟩

#print axioms body_success_scalar_canonical
end AspisR1FastDotsActualScalarParserCanonical
