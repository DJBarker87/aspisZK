import NEG_FoldAssociation
import JFn_LineTotal
import SAQ_LineArrays
set_option autoImplicit false
noncomputable section
namespace NEI_LineDomains
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentWide AspisR1CurrentWide.Proof
open SAQ_LineSource

/-- No inverse canonicality or unused-cell predicate is imposed. -/
def Domain (alpha : E) (rows : Array E 4#usize) : Prop :=
  CanonicalWide alpha ∧ ∀ x ∈ rows.val, CanonicalWide x

def Intermediates {alpha a b c d out : E} {lx ly lz : U32}
    (cut : Cuts alpha a b c d lx ly lz out) : Prop :=
  CanonicalWide cut.we ∧
  CanonicalWide cut.we1 ∧
  CanonicalWide cut.we2 ∧
  CanonicalWide cut.h0 ∧
  CanonicalWide cut.we3 ∧
  CanonicalWide cut.we4 ∧
  CanonicalWide cut.h2 ∧
  CanonicalWide cut.we5 ∧
  CanonicalWide cut.c0 ∧
  CanonicalWide cut.we6 ∧
  CanonicalWide cut.c1 ∧
  CanonicalWide cut.we7 ∧
  CanonicalWide cut.h1 ∧
  CanonicalWide cut.we8 ∧
  CanonicalWide cut.h3 ∧
  CanonicalWide cut.we9 ∧
  CanonicalWide cut.we10 ∧
  CanonicalWide cut.we11 ∧
  CanonicalWide cut.we12 ∧
  CanonicalWide cut.we13 ∧
  CanonicalWide out

theorem same_site_domains (alpha a b c d out : E) (lx ly lz : U32)
    (cut : Cuts alpha a b c d lx ly lz out)
    (hAlpha : CanonicalWide alpha) (ha : CanonicalWide a) (hb : CanonicalWide b)
    (hc : CanonicalWide c) (hd : CanonicalWide d) : Intermediates cut := by
  have Cwe : CanonicalWide cut.we := (wide_add_success a b cut.we ha hb cut.Hwe).1
  have Cwe1 : CanonicalWide cut.we1 := (wide_add_success cut.we c cut.we1 Cwe hc cut.Hwe1).1
  have Cwe2 : CanonicalWide cut.we2 := (wide_add_success cut.we1 d cut.we2 Cwe1 hd cut.Hwe2).1
  have Ch0 : CanonicalWide cut.h0 := (SAQ_LineSource.scale cut.we2 cut.h0 quarter cut.Hh0).1
  have Cwe3 : CanonicalWide cut.we3 := wide_sub_success_canonical cut.we c cut.we3 Cwe hc cut.Hwe3
  have Cwe4 : CanonicalWide cut.we4 := wide_sub_success_canonical cut.we3 d cut.we4 Cwe3 hd cut.Hwe4
  have Ch2 : CanonicalWide cut.h2 := (SAQ_LineSource.scale cut.we4 cut.h2 cut.m cut.Hh2).1
  have Cwe5 : CanonicalWide cut.we5 := wide_sub_success_canonical a b cut.we5 ha hb cut.Hwe5
  have Cc0 : CanonicalWide cut.c0 := (SAQ_LineSource.scale cut.we5 cut.c0 cut.m1 cut.Hc0).1
  have Cwe6 : CanonicalWide cut.we6 := wide_sub_success_canonical d c cut.we6 hd hc cut.Hwe6
  have Cc1 : CanonicalWide cut.c1 := (SAQ_LineSource.scale cut.we6 cut.c1 cut.m2 cut.Hc1).1
  have Cwe7 : CanonicalWide cut.we7 := (wide_add_success cut.c0 cut.c1 cut.we7 Cc0 Cc1 cut.Hwe7).1
  have Ch1 : CanonicalWide cut.h1 := (SAQ_LineSource.scale cut.we7 cut.h1 1073741824#u32 cut.Hh1).1
  have Cwe8 : CanonicalWide cut.we8 := wide_sub_success_canonical cut.c0 cut.c1 cut.we8 Cc0 Cc1 cut.Hwe8
  have Ch3 : CanonicalWide cut.h3 := (SAQ_LineSource.scale cut.we8 cut.h3 cut.m3 cut.Hh3).1
  have Cwe9 : CanonicalWide cut.we9 := (SAQ_RawWide.mul_exact alpha cut.h3 cut.we9 cut.Hwe9).1
  have Cwe10 : CanonicalWide cut.we10 := (wide_add_success cut.h2 cut.we9 cut.we10 Ch2 Cwe9 cut.Hwe10).1
  have Cwe11 : CanonicalWide cut.we11 := (SAQ_RawWide.mul_exact alpha cut.we10 cut.we11 cut.Hwe11).1
  have Cwe12 : CanonicalWide cut.we12 := (wide_add_success cut.h1 cut.we11 cut.we12 Ch1 Cwe11 cut.Hwe12).1
  have Cwe13 : CanonicalWide cut.we13 := (SAQ_RawWide.mul_exact alpha cut.we12 cut.we13 cut.Hwe13).1
  have Cout : CanonicalWide out := (wide_add_success cut.h0 cut.we13 out Ch0 Cwe13 cut.Hout).1
  exact ⟨Cwe,Cwe1,Cwe2,Ch0,Cwe3,Cwe4,Ch2,Cwe5,Cc0,Cwe6,Cc1,Cwe7,Ch1,Cwe8,Ch3,Cwe9,Cwe10,Cwe11,Cwe12,Cwe13,Cout⟩

theorem total (alpha : E) (rows : Array E 4#usize) (inverse : Array U32 5#usize)
    (domain : Domain alpha rows) :
    ∃ out, NEG_FoldsTypes.line_fold_with_inverses alpha rows inverse = ok out ∧
      CanonicalWide out := by
  obtain ⟨a,b,c,d,rfl⟩ := SAQ_LineArrays.four rows
  obtain ⟨ix,iy,lx,ly,lz,rfl⟩ := SAQ_LineArrays.five inverse
  have ha := domain.2 a (by simp [Array.make])
  have hb := domain.2 b (by simp [Array.make])
  have hc := domain.2 c (by simp [Array.make])
  have hd := domain.2 d (by simp [Array.make])
  rw [NEG_FoldAssociation.line]
  exact JFn_LineTotal.source alpha a b c d ix iy lx ly lz domain.1 ha hb hc hd

#print axioms same_site_domains
#print axioms total
end NEI_LineDomains
end
