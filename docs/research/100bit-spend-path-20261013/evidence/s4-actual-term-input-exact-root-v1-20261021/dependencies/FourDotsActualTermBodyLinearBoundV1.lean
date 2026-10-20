import FourDotsActualEightLimbLinearCallV1
import AspisR1FastDotsCurrentM31OpsBinding
import AspisR1DecodeKFullV10ParserCanonicality
import AspisR1FastDotsCurrent.FunsOpsV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualTermBodyLinearBoundV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := Std.U32
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Range := core.ops.range.Range Usize
abbrev TermBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body
abbrev InnerLoop := AspisR1FastDotsActualInnerLoopLinearBoundV1.InnerLoop
abbrev cap : Nat := AspisR1FastDotsActualInnerLoopLinearBoundV1.cap

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Success of the exact emitted per-term body exposes its actual parser,
    wide-limb conversion, and fixed eight-limb reduction call. The operation
    bindings are explicit, so this does not trust the generated external stubs. -/
theorem term_body_success_inner_call
    (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hparser : ops.m31FromBytes = AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes)
    (hbody : TermBody ops a a1 slot iter sums = .ok (.cont (iter', sums'))) :
    ∃ term : Usize, ∃ bytes : Array U8 4#usize, ∃ scalar : AspisR1FastDotsCurrent.aspis_core.field.M31,
      ∃ wide : Wide, ∃ coeff : Array U32 8#usize,
      ops.m31FromBytes bytes = .ok (some scalar) ∧
      scalar.val < AspisR1DecodeKFullV10.aspis_core.field.P.val ∧
      Array.index_usize a1 term = .ok wide ∧
      ops.wideToLimbs wide = .ok coeff ∧
      InnerLoop ops { start := 0#usize, «end» := 8#usize } sums scalar coeff = .ok sums' := by
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
      exact ⟨term, bytes, scalar, wide, coeff,
        by simpa only [hparser, hparsedEq] using hparse,
        hscalar, hwideRead, hcoeff, hloop'⟩

/-- Applying the source-bound actual term call increases the uniform limb
    bound by at most one cap. Canonicality of the indexed Wide input is kept as
    a caller premise. -/
theorem term_body_success_linear_bound
    (ops : Ops) (k : Nat) (hk : k ≤ 3)
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hcount : ops.wideLimbCount = .ok 8#usize)
    (hparser : ops.m31FromBytes = AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes)
    (hwide : ∀ x : Wide, ops.wideToLimbs x = AspisR1EbyKPushWideToQ.toLimbs x)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hinput : ∀ i : Fin 8,
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell sums i ≤ k * cap)
    (hbody : TermBody ops a a1 slot iter sums = .ok (.cont (iter', sums'))) :
    ∀ i : Fin 8,
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell sums' i ≤ (k + 1) * cap := by
  obtain ⟨term, bytes, scalar, wide, coeff, hparse, hscalar, hread, hcoeff, hloop⟩ :=
    term_body_success_inner_call ops a a1 slot iter iter' sums sums' hcount hparser hbody
  have hidx : term.val < a1.val.length := by
    by_contra hnot
    have hnone : a1[term]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at hread
    rw [hnone] at hread
    cases hread
  have hidx' : term.val < 29 := by simpa [a1.property] using hidx
  have hget : wide = a1.val[term.val]'(by simpa [a1.property] using hidx') := by
    obtain ⟨x, hspec, hx⟩ := WP.spec_imp_exists
      (Array.index_usize_spec a1 term (by simpa [a1.property] using hidx'))
    exact Result.ok.inj (hread.symm.trans hspec) |>.trans hx
  have hwideCanonical : AspisR1FastDotsWideLimbCanonical.CoordinateBound wide := by
    rw [hget]
    exact hcoords ⟨term.val, hidx'⟩
  have hscalar' : scalar.val < 2147483647 := by
    simpa [AspisR1DecodeKFullV10.aspis_core.field.P] using hscalar
  have hcall : AspisR1EbyKPushWideToQ.toLimbs wide = .ok coeff := by
    rw [← hwide wide]
    exact hcoeff
  exact AspisR1FastDotsActualEightLimbLinearCallV1.current_wide_inner_loop_linear_bound
    ops k hk wide hwideCanonical { start := 0#usize, «end» := 8#usize }
    sums sums' scalar coeff hcall hinput hscalar' hloop

#print axioms term_body_success_inner_call
#print axioms term_body_success_linear_bound

/-- Bind the three operations used by the emitted term body to the actual
    retained M31 parser, limb-count constant and wide-to-limbs conversion. -/
def withCurrentTermBodyOps (ops : Ops) : Ops :=
  AspisR1FastDotsCurrentM31OpsBinding.withCurrentM31ParserReducer
    (AspisR1FastDotsActualEightLimbCallV1.withCurrentWideOps
      (AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8 ops))

theorem current_term_body_success_linear_bound
    (ops : Ops) (k : Nat) (hk : k ≤ 3)
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hinput : ∀ i : Fin 8,
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell sums i ≤ k * cap)
    (hbody : TermBody (withCurrentTermBodyOps ops) a a1 slot iter sums =
      .ok (.cont (iter', sums'))) :
    ∀ i : Fin 8,
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell sums' i ≤ (k + 1) * cap := by
  have hcount : (withCurrentTermBodyOps ops).wideLimbCount = .ok 8#usize := rfl
  have hparser : (withCurrentTermBodyOps ops).m31FromBytes =
      AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes := rfl
  have hwide : ∀ x : Wide,
      (withCurrentTermBodyOps ops).wideToLimbs x = AspisR1EbyKPushWideToQ.toLimbs x := by
    intro x
    rfl
  exact term_body_success_linear_bound (withCurrentTermBodyOps ops) k hk a a1 slot
    iter iter' sums sums' hcount hparser hwide hcoords hinput hbody

#print axioms current_term_body_success_linear_bound

end AspisR1FastDotsActualTermBodyLinearBoundV1
