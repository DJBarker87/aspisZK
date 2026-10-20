import FourDotsActualTermTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTermTraceBoundsRootV1
open AspisR1FastDotsActualTermTraceRootV1

theorem matched_contribution_product_le
    (c : Contribution) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (iter iter' : Range)
    (hcoord : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hmatch : c.matches a a1 slot iter iter') :
    ∀ j : Fin 8, c.product j ≤ cap := by
  rcases hmatch with ⟨hnext,hbytes,hparse,hscalar,hread,hcoeff⟩
  have hidx : c.term.val < a1.val.length := by
    by_contra hnot
    have hnone : a1[c.term]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at hread
    rw [hnone] at hread
    cases hread
  have hidx' : c.term.val < 29 := by simpa [a1.property] using hidx
  have hget : c.wide = a1.val[c.term.val]'(by simpa [a1.property] using hidx') := by
    obtain ⟨x,hspec,hx⟩ := WP.spec_imp_exists
      (Array.index_usize_spec a1 c.term (by simpa [a1.property] using hidx'))
    exact Result.ok.inj (hread.symm.trans hspec) |>.trans hx
  have hcanonical : AspisR1FastDotsWideLimbCanonical.CoordinateBound c.wide := by
    rw [hget]
    exact hcoord ⟨c.term.val,hidx'⟩
  have hcc := AspisR1FastDotsActualEightLimbCallV1.current_wide_coefficients_canonical
    c.wide hcanonical c.coeff hcoeff
  intro j
  have hc : AspisR1FastDotsActualLimbLoopExactRootV1.coeffCell c.coeff j ≤ 2147483646 := by
    have h := hcc j
    change AspisR1FastDotsActualLimbLoopExactRootV1.coeffCell c.coeff j < 2147483647 at h
    omega
  have hs : c.scalar.val ≤ 2147483646 := by omega
  have hm := Nat.mul_le_mul hc hs
  simpa only [Contribution.product,cap,AspisR1FastDotsActualTermLoopLinearBoundV1.cap,
    AspisR1FastDotsActualInnerLoopLinearBoundV1.cap,pow_two] using hm

/-- Product caps for the retained contribution list are consequences of the
same actual coefficient reads and canonical source values. -/
theorem actual_trace_products_bounded
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (sums out : Array U64 8#usize) (cs : List Contribution)
    (hcoord : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (htrace : ActualTermTrace ops a a1 slot iter sums out cs) :
    ∀ c ∈ cs, ∀ j : Fin 8, c.product j ≤ cap := by
  induction htrace with
  | done iter sums hbody => intro c hc; cases hc
  | step c tail hbody hmatch hvalue htail ih =>
      intro x hx
      rcases List.mem_cons.mp hx with heq | htailmem
      · subst x
        exact matched_contribution_product_le c a a1 slot _ _ hcoord hmatch
      · exact ih x htailmem
#print axioms matched_contribution_product_le
#print axioms actual_trace_products_bounded
end AspisR1FastDotsActualTermTraceBoundsRootV1
