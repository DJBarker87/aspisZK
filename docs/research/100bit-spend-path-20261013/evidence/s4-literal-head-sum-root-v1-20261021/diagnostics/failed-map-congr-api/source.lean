import S4QueryValuesFourCallbackFieldResultV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsLiteralHeadSumRootV1
open AspisR1FastDotsHeadFieldAlgebraRootV1 (sourceProduct embedM31)
open AspisR1FastDotsTailFieldProductRootV1 (wideDecoded TowerWide)
open AspisR1FastDotsActualTermSourceMeaningRootV1 (SourceMeaning)
abbrev Contribution := AspisR1FastDotsActualTermTraceRootV1.Contribution
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact

/-- Literal term value depends only on source bytes and coefficient index,
not on an extracted execution witness. Invalid shape is assigned zero; the
source-meaning theorem below proves that branch is never used by accepted terms. -/
def headTermValue (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Nat) : TowerWide :=
  match g.val[term]? with
  | none => 0
  | some wide =>
    let bytes := a.val.slice (slot*120+term*4) (slot*120+term*4+4)
    if h : bytes.length=(4#usize).val then
      wideDecoded wide * embedM31 (core.num.U32.from_le_bytes ⟨bytes,h⟩).val
    else 0

theorem source_product_literal (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (c : Contribution) (h : SourceMeaning a g slot c) :
    sourceProduct c=headTermValue a g slot.val c.term.val := by
  rcases h with ⟨_hbound,hbytes,hscalar,hwide,_hcoeff⟩
  have hlen : (a.val.slice (slot.val*120+c.term.val*4)
      (slot.val*120+c.term.val*4+4)).length=(4#usize).val := by
    rw [← hbytes]
    exact c.bytes.property
  simp only [headTermValue,hwide,dif_pos hlen]
  have heq : (⟨a.val.slice (slot.val*120+c.term.val*4)
      (slot.val*120+c.term.val*4+4),hlen⟩ : Array Std.U8 4#usize)=c.bytes :=
    Subtype.ext hbytes.symm
  rw [heq]
  simp only [sourceProduct,hscalar]

theorem source_head_sum_literal (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (cs : List Contribution)
    (hindices : cs.map (fun c=>c.term.val)=List.range' 0 26)
    (hmeaning : ∀ c∈cs, SourceMeaning a g slot c) :
    (cs.map sourceProduct).sum=
      ((List.range' 0 26).map (headTermValue a g slot.val)).sum := by
  have hmap : cs.map sourceProduct=cs.map (fun c=>headTermValue a g slot.val c.term.val) :=
    List.map_congr_left.mpr (fun c hc=>source_product_literal a g slot c (hmeaning c hc))
  rw [hmap]
  have hm := congrArg (List.map (headTermValue a g slot.val)) hindices
  simp only [List.map_map,Function.comp_def] at hm
  rw [hm]
#print axioms source_product_literal
#print axioms source_head_sum_literal
end AspisR1FastDotsLiteralHeadSumRootV1
