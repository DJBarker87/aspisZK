import FourDotsActualTermInputTraceRootV1
import FourDotsActualLimbLoopExactRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTermExactRootV1
open AspisR1FastDotsActualTermBodyLinearBoundV1
open AspisR1FastDotsActualTermInputTraceRootV1
abbrev U8 := Std.U8
abbrev U32 := Std.U32
abbrev U64 := Std.U64

/-- Exact source term update retains the actual input bytes, parser result,
wide read and coefficient conversion supplying the same scalar products. -/
theorem current_term_body_success_exact
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hinput : ∀ j : Fin 8,
      AspisR1FastDotsActualLimbLoopExactRootV1.cell sums j ≤
        3 * AspisR1FastDotsActualLimbLoopExactRootV1.cap)
    (hbody : TermBody (withCurrentTermBodyOps ops) a a1 slot iter sums =
      .ok (.cont (iter',sums'))) :
    ∃ (term : Usize) (bytes : Array U8 4#usize)
      (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
      (wide : Wide) (coeff : Array U32 8#usize),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some term,iter') ∧
      TermBytesTrace a slot term bytes ∧
      AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes bytes = .ok (some scalar) ∧
      scalar.val < 2147483647 ∧
      Array.index_usize a1 term = .ok wide ∧
      AspisR1EbyKPushWideToQ.toLimbs wide = .ok coeff ∧
      ∀ j : Fin 8, AspisR1FastDotsActualLimbLoopExactRootV1.cell sums' j =
        AspisR1FastDotsActualLimbLoopExactRootV1.cell sums j +
          AspisR1FastDotsActualLimbLoopExactRootV1.coeffCell coeff j * scalar.val := by
  obtain ⟨term,bytes,scalar,wide,coeff,hnext,hbytes,hparse,hscalar,hread,hcoeff,hloop⟩ :=
    actual_term_body_success_input_trace (withCurrentTermBodyOps ops)
      a a1 slot iter iter' sums sums' rfl rfl hbody
  have hidx : term.val < a1.val.length := by
    by_contra hnot
    have hnone : a1[term]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at hread
    rw [hnone] at hread
    cases hread
  have hidx' : term.val < 29 := by simpa [a1.property] using hidx
  have hget : wide = a1.val[term.val]'(by simpa [a1.property] using hidx') := by
    obtain ⟨x,hspec,hx⟩ := WP.spec_imp_exists
      (Array.index_usize_spec a1 term (by simpa [a1.property] using hidx'))
    exact Result.ok.inj (hread.symm.trans hspec) |>.trans hx
  have hcanonical : AspisR1FastDotsWideLimbCanonical.CoordinateBound wide := by
    rw [hget]
    exact hcoords ⟨term.val,hidx'⟩
  have hcall : AspisR1EbyKPushWideToQ.toLimbs wide = .ok coeff := hcoeff
  have hcoeffCanonical :=
    AspisR1FastDotsActualEightLimbCallV1.current_wide_coefficients_canonical
      wide hcanonical coeff hcall
  have hscalar' : scalar.val < 2147483647 := by
    change scalar.val < 2147483647 at hscalar
    exact hscalar
  have hexact := AspisR1FastDotsActualLimbLoopExactRootV1.actual_eight_limb_loop_success_exact
    (withCurrentTermBodyOps ops) coeff sums sums' scalar hcoeffCanonical hinput hscalar' hloop
  exact ⟨term,bytes,scalar,wide,coeff,hnext,hbytes,hparse,hscalar',hread,hcall,hexact⟩
#print axioms current_term_body_success_exact
end AspisR1FastDotsActualTermExactRootV1
