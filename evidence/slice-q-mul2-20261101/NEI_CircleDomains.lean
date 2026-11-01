import NEI_LineDomains
import JFr_TX2_CircleTotal
import FIp_CircleCuts
set_option autoImplicit false
noncomputable section
namespace NEI_CircleDomains
open Aeneas Aeneas.Std Result AspisR1 AspisR1CurrentWide AspisR1CurrentWide.Proof
open FIp_CircleCuts
abbrev Domain := NEI_LineDomains.Domain

def Intermediates {alpha a b c d out : E} {ix iy : U32}
    (cut : Cuts alpha a b c d ix iy out) : Prop :=
  CanonicalWide cut.we ∧
  CanonicalWide cut.we1 ∧
  CanonicalWide cut.we2 ∧
  CanonicalWide cut.h0 ∧
  CanonicalWide cut.we3 ∧
  CanonicalWide cut.we4 ∧
  CanonicalWide cut.we5 ∧
  CanonicalWide cut.h1 ∧
  CanonicalWide cut.we6 ∧
  CanonicalWide cut.we7 ∧
  CanonicalWide cut.h2 ∧
  CanonicalWide cut.we8 ∧
  CanonicalWide cut.we9 ∧
  CanonicalWide cut.h3 ∧
  CanonicalWide cut.we10 ∧
  CanonicalWide cut.we11 ∧
  CanonicalWide cut.we12 ∧
  CanonicalWide cut.we13 ∧
  CanonicalWide cut.we14 ∧
  CanonicalWide out

theorem same_site_domains (alpha a b c d out : E) (ix iy : U32)
    (cut : Cuts alpha a b c d ix iy out)
    (ha : CanonicalWide a) (hb : CanonicalWide b)
    (hc : CanonicalWide c) (hd : CanonicalWide d) : Intermediates cut := by
  have Cwe : CanonicalWide cut.we := (wide_add_success a b cut.we ha hb cut.Hwe).1
  have Cwe1 : CanonicalWide cut.we1 := (wide_add_success cut.we c cut.we1 Cwe hc cut.Hwe1).1
  have Cwe2 : CanonicalWide cut.we2 := (wide_add_success cut.we1 d cut.we2 Cwe1 hd cut.Hwe2).1
  have Ch0 : CanonicalWide cut.h0 := (SAQ_LineSource.scale cut.we2 cut.h0 SAQ_LineSource.quarter cut.Hh0).1
  have Cwe3 : CanonicalWide cut.we3 := NEI_LineDomains.sub_canonical a b cut.we3 ha hb cut.Hwe3
  have Cwe4 : CanonicalWide cut.we4 := NEI_LineDomains.sub_canonical cut.we3 c cut.we4 Cwe3 hc cut.Hwe4
  have Cwe5 : CanonicalWide cut.we5 := (wide_add_success cut.we4 d cut.we5 Cwe4 hd cut.Hwe5).1
  have Ch1 : CanonicalWide cut.h1 := (SAQ_LineSource.scale cut.we5 cut.h1 cut.m cut.Hh1).1
  have Cwe6 : CanonicalWide cut.we6 := NEI_LineDomains.sub_canonical cut.we c cut.we6 Cwe hc cut.Hwe6
  have Cwe7 : CanonicalWide cut.we7 := NEI_LineDomains.sub_canonical cut.we6 d cut.we7 Cwe6 hd cut.Hwe7
  have Ch2 : CanonicalWide cut.h2 := (SAQ_LineSource.scale cut.we7 cut.h2 cut.m1 cut.Hh2).1
  have Cwe8 : CanonicalWide cut.we8 := (wide_add_success cut.we3 c cut.we8 Cwe3 hc cut.Hwe8).1
  have Cwe9 : CanonicalWide cut.we9 := NEI_LineDomains.sub_canonical cut.we8 d cut.we9 Cwe8 hd cut.Hwe9
  have Ch3 : CanonicalWide cut.h3 := (SAQ_LineSource.scale cut.we9 cut.h3 cut.m2 cut.Hh3).1
  have Cwe10 : CanonicalWide cut.we10 := (SAQ_RawWide.mul_exact alpha cut.h3 cut.we10 cut.Hwe10).1
  have Cwe11 : CanonicalWide cut.we11 := (wide_add_success cut.h2 cut.we10 cut.we11 Ch2 Cwe10 cut.Hwe11).1
  have Cwe12 : CanonicalWide cut.we12 := (SAQ_RawWide.mul_exact alpha cut.we11 cut.we12 cut.Hwe12).1
  have Cwe13 : CanonicalWide cut.we13 := (wide_add_success cut.h1 cut.we12 cut.we13 Ch1 Cwe12 cut.Hwe13).1
  have Cwe14 : CanonicalWide cut.we14 := (SAQ_RawWide.mul_exact alpha cut.we13 cut.we14 cut.Hwe14).1
  have Cout : CanonicalWide out := (wide_add_success cut.h0 cut.we14 out Ch0 Cwe14 cut.Hout).1
  exact ⟨Cwe,Cwe1,Cwe2,Ch0,Cwe3,Cwe4,Cwe5,Ch1,Cwe6,Cwe7,Ch2,Cwe8,Cwe9,Ch3,Cwe10,Cwe11,Cwe12,Cwe13,Cwe14,Cout⟩

theorem total (alpha : E) (a : Array E 4#usize) (inverse : Array U32 5#usize)
    (domain : Domain alpha a) :
    ∃ out, FIp_CircleSource.circle alpha a inverse = ok out ∧ CanonicalWide out := by
  obtain ⟨a,b,c,d,rfl⟩ := SAQ_LineArrays.four a
  obtain ⟨ix,iy,lx,ly,lz,rfl⟩ := SAQ_LineArrays.five inverse
  have ha := domain.2 a (by simp [Array.make])
  have hb := domain.2 b (by simp [Array.make])
  have hc := domain.2 c (by simp [Array.make])
  have hd := domain.2 d (by simp [Array.make])
  exact JFr_TX2_CircleTotal.source alpha a b c d ix iy lx ly lz domain.1 ha hb hc hd

#print axioms same_site_domains
#print axioms total
end NEI_CircleDomains
end
