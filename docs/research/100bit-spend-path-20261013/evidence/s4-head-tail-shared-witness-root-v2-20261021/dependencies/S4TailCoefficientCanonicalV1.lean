import FourDotsActualTailInputMeaningRootV1
import EbyKPowerValueCanonicalToPushV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailCoefficientCanonicalV1
open AspisR1FastDotsActualTailBodyTraceRootV1
abbrev Wide := AspisR1FastDotsActualCallbackTailTraceRootV1.Wide
abbrev PushCanonical := AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
def CoordBound (x : Wide) : Prop :=
  x.c0.c0.a.val < 2147483647 ∧ x.c0.c0.b.val < 2147483647 ∧
  x.c0.c1.a.val < 2147483647 ∧ x.c0.c1.b.val < 2147483647 ∧
  x.c1.c0.a.val < 2147483647 ∧ x.c1.c0.b.val < 2147483647 ∧
  x.c1.c1.a.val < 2147483647 ∧ x.c1.c1.b.val < 2147483647

private theorem index_success_eq {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) :
    ∃ hx : i.val < n.val, x = a.val[i.val]'(by simpa [a.property] using hx) := by
  have hlen : i.val < a.val.length := by
    by_contra hnot
    have hnone : a[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  have hi : i.val < n.val := by simpa [a.property] using hlen
  have hlen' : i.val < a.val.length := by simpa [a.property] using hi
  obtain ⟨y, hspec, hy⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hlen')
  have hxy : x = y := Result.ok.inj (h.symm.trans hspec)
  exact ⟨hi, hxy.trans hy⟩

/-- A coefficient read from the actual 29-entry source array inherits the
    coordinate bounds of that exact source slot. -/
theorem read_coordinate_bound
    (g : Array Wide 29#usize) (i : Usize) (x : Wide)
    (hcoords : ∀ j : Fin 29, CoordBound (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hread : Array.index_usize g i = .ok x) : CoordBound x := by
  obtain ⟨hi,hx⟩ := index_success_eq g i x hread
  rw [hx]
  exact hcoords ⟨i.val, by simpa [g.property] using hi⟩

/-- The same source read is canonical in the actual EbyK push carrier. -/
theorem read_push_canonical
    (g : Array Wide 29#usize) (i : Usize) (x : Wide)
    (hcoords : ∀ j : Fin 29, CoordBound (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hread : Array.index_usize g i = .ok x) : PushCanonical x := by
  have hcoord := read_coordinate_bound g i x hcoords hread
  rcases hcoord with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  change AspisR1CurrentWideMul.CanonicalWide
    (AspisR1EbyKPowerValueCanonicalToPush.pushToSource x)
  change ((x.c0.c0.a.val < 2147483647 ∧ x.c0.c0.b.val < 2147483647) ∧
    (x.c0.c1.a.val < 2147483647 ∧ x.c0.c1.b.val < 2147483647)) ∧
    ((x.c1.c0.a.val < 2147483647 ∧ x.c1.c0.b.val < 2147483647) ∧
    (x.c1.c1.a.val < 2147483647 ∧ x.c1.c1.b.val < 2147483647))
  exact ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩

/-- Each contribution in a retained tail trace is canonical by the exact
    coefficient index/read witness and the corresponding source coordinate. -/
theorem trace_coefficients_canonical
    (ops : AspisR1FastDotsActualCallbackTailTraceRootV1.Ops)
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter : AspisR1FastDotsActualTailBodyTraceRootV1.Range)
    (old out : AspisR1FastDotsActualCallbackTailTraceRootV1.Tail)
    (cs : List Contribution)
    (hcoords : ∀ j : Fin 29, CoordBound (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (htrace : AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace ops a g slot iter old out cs) :
    ∀ c ∈ cs, PushCanonical c.coefficient := by
  intro c hc
  have hmeaning := AspisR1FastDotsActualTailInputMeaningRootV1.actual_tail_trace_source_meanings
    ops a g slot iter old out cs htrace c hc
  rcases hmeaning with ⟨i, _hindex, hread, _hbytes⟩
  exact read_push_canonical g i c.coefficient hcoords hread

#print axioms read_coordinate_bound
#print axioms read_push_canonical
#print axioms trace_coefficients_canonical
end AspisR1FastDotsTailCoefficientCanonicalV1
