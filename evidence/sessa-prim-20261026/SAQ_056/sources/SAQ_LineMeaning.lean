import SAQ_LineSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineMeaning
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof SAQ_LineSource
attribute [local irreducible] AspisR1CurrentWide.Proof.decodeWide SAQ_LineSource.decodeBase R1ZCircleFoldMathV1.sourceLineFold

private theorem values4_0 {K : Type} (a b c d : K) : values4 a b c d 0=a := rfl
private theorem values4_1 {K : Type} (a b c d : K) : values4 a b c d 1=b := rfl
private theorem values4_2 {K : Type} (a b c d : K) : values4 a b c d 2=c := rfl
private theorem values4_3 {K : Type} (a b c d : K) : values4 a b c d 3=d := rfl
private theorem decodeQuarter : decodeBase quarter=R1ZCircleFoldMathV1.rustQuarter := rfl
private theorem decodeHalf : decodeBase (1073741824#u32)=R1ZCircleFoldMathV1.rustHalf := rfl

theorem on_cuts (alpha a b c d out : E) (lx ly lz : U32)
    (cut : Cuts alpha a b c d lx ly lz out) :
    CanonicalWide out ∧ decodeWide out =
      R1ZCircleFoldMathV1.sourceLineFold (decodeWide alpha)
        (values4 (decodeWide a) (decodeWide b) (decodeWide c) (decodeWide d))
        (decodeBase lx) (decodeBase ly) (decodeBase lz) := by
  rcases cut with ⟨we,we1,we2,h0,we3,we4,m,h2,we5,m1,c0,we6,m2,c1,we7,h1,we8,m3,h3,we9,we10,we11,we12,we13,Hwe,Hwe1,Hwe2,Hh0,Hwe3,Hwe4,Hm,Hh2,Hwe5,Hm1,Hc0,Hwe6,Hm2,Hc1,Hwe7,Hh1,Hwe8,Hm3,Hh3,Hwe9,Hwe10,Hwe11,Hwe12,Hwe13,h⟩
  have Ewe := SAQ_RawWide.add_exact a b we Hwe
  have Ewe1 := SAQ_RawWide.add_exact we c we1 Hwe1
  have Ewe2 := SAQ_RawWide.add_exact we1 d we2 Hwe2
  obtain ⟨Ch0,Eh0⟩ := scale we2 h0 quarter Hh0
  have Ewe3 := SAQ_RawWide.sub_exact we c we3 Hwe3
  have Ewe4 := SAQ_RawWide.sub_exact we3 d we4 Hwe4
  obtain ⟨Cm,Em⟩ := baseMul quarter lz m Hm
  obtain ⟨Ch2,Eh2⟩ := scale we4 h2 m Hh2
  have Ewe5 := SAQ_RawWide.sub_exact a b we5 Hwe5
  obtain ⟨Cm1,Em1⟩ := baseMul 1073741824#u32 lx m1 Hm1
  obtain ⟨Cc0,Ec0⟩ := scale we5 c0 m1 Hc0
  have Ewe6 := SAQ_RawWide.sub_exact d c we6 Hwe6
  obtain ⟨Cm2,Em2⟩ := baseMul 1073741824#u32 ly m2 Hm2
  obtain ⟨Cc1,Ec1⟩ := scale we6 c1 m2 Hc1
  have Ewe7 := SAQ_RawWide.add_exact c0 c1 we7 Hwe7
  obtain ⟨Ch1,Eh1⟩ := scale we7 h1 1073741824#u32 Hh1
  have Ewe8 := SAQ_RawWide.sub_exact c0 c1 we8 Hwe8
  obtain ⟨Cm3,Em3⟩ := baseMul 1073741824#u32 lz m3 Hm3
  obtain ⟨Ch3,Eh3⟩ := scale we8 h3 m3 Hh3
  obtain ⟨Cwe9,Ewe9⟩ := SAQ_RawWide.mul_exact alpha h3 we9 Hwe9
  have Ewe10 := SAQ_RawWide.add_exact h2 we9 we10 Hwe10
  obtain ⟨Cwe11,Ewe11⟩ := SAQ_RawWide.mul_exact alpha we10 we11 Hwe11
  have Ewe12 := SAQ_RawWide.add_exact h1 we11 we12 Hwe12
  obtain ⟨Cwe13,Ewe13⟩ := SAQ_RawWide.mul_exact alpha we12 we13 Hwe13
  obtain ⟨Cout,Eout⟩ := wide_add_success h0 we13 out Ch0 Cwe13 h
  refine ⟨Cout,?_⟩
  rw [Ewe2,Ewe1,Ewe] at Eh0
  rw [Em,Ewe4,Ewe3,Ewe] at Eh2
  rw [Em1,Ewe5] at Ec0
  rw [Em2,Ewe6] at Ec1
  rw [Ewe7,Ec0,Ec1] at Eh1
  rw [Em3,Ewe8,Ec0,Ec1] at Eh3
  rw [Ewe13,Ewe12,Ewe11,Ewe10,Ewe9] at Eout
  rw [Eh0,Eh1,Eh2,Eh3] at Eout
  simpa only [R1ZCircleFoldMathV1.sourceLineFold,values4_0,values4_1,values4_2,
    values4_3,decodeQuarter,decodeHalf] using Eout


#print axioms on_cuts
end AspisR1.SAQ_LineMeaning
end
