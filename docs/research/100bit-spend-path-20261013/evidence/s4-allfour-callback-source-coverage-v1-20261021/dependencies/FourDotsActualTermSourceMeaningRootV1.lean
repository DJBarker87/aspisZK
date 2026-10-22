import FourDotsActualTermTraceRootV1
import FourDotsActualTermByteOffsetsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTermSourceMeaningRootV1
open AspisR1FastDotsActualTermTraceRootV1
abbrev U8 := Std.U8
abbrev U64 := Std.U64

/-- Literal source meanings of a retained contribution, before any
polynomial/relation interpretation of the source buffers. -/
def SourceMeaning (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (c : Contribution) : Prop :=
  c.term.val < 29 ∧
  c.bytes.val = a.val.slice (slot.val*120+c.term.val*4) (slot.val*120+c.term.val*4+4) ∧
  c.scalar = core.num.U32.from_le_bytes c.bytes ∧
  a1.val[c.term.val]? = some c.wide ∧
  c.coeff = AspisR1FastDotsWideLimbCanonical.limbArray c.wide

/-- Actual parse/read/conversion successes derive the literal input meaning;
no independent byte or decoded-value equation is assumed. -/
theorem matched_contribution_source_meaning
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (c : Contribution)
    (hmatch : c.matches a a1 slot iter iter') : SourceMeaning a a1 slot c := by
  rcases hmatch with ⟨hnext,hbytes,hparse,hscalar,hread,hcoeff⟩
  have hidx : c.term.val < a1.val.length := by
    by_contra hnot
    have hnone : a1[c.term]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at hread
    rw [hnone] at hread
    cases hread
  have hidx' : c.term.val < 29 := by simpa [a1.property] using hidx
  have hget : c.wide = a1.val[c.term.val]'hidx := by
    obtain ⟨x,hspec,hx⟩ := WP.spec_imp_exists (Array.index_usize_spec a1 c.term hidx)
    exact Result.ok.inj (hread.symm.trans hspec) |>.trans hx
  have hbyteMeaning := AspisR1FastDotsActualTermByteOffsetsRootV1.actual_term_bytes_exact_offset
    a slot c.term c.bytes hbytes
  have hscalarMeaning := AspisR1FastDotsActualTermByteContentsRootV1.source_parser_success_word
    c.bytes c.scalar hparse
  have hcoeffMeaning : c.coeff = AspisR1FastDotsWideLimbCanonical.limbArray c.wide :=
    Result.ok.inj (hcoeff.symm.trans (AspisR1FastDotsWideLimbCanonical.toLimbs_actual_value c.wide))
  have hwideMeaning : a1.val[c.term.val]? = some c.wide := by
    rw [List.getElem?_eq_getElem hidx,hget]
  exact ⟨hidx',hbyteMeaning,hscalarMeaning,hwideMeaning,hcoeffMeaning⟩

theorem actual_trace_source_meanings
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (sums out : Array U64 8#usize) (cs : List Contribution)
    (htrace : ActualTermTrace ops a a1 slot iter sums out cs) :
    ∀ c ∈ cs, SourceMeaning a a1 slot c := by
  induction htrace with
  | done iter sums hbody => intro c hc; cases hc
  | step c tail hbody hmatch hvalue htail ih =>
      intro x hx
      rcases List.mem_cons.mp hx with heq | htailmem
      · subst x
        exact matched_contribution_source_meaning a a1 slot _ _ c hmatch
      · exact ih x htailmem
#print axioms matched_contribution_source_meaning
#print axioms actual_trace_source_meanings
end AspisR1FastDotsActualTermSourceMeaningRootV1
