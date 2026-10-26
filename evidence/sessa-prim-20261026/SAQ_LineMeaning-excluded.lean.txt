import SAQ_LineAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineMeaning
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof SAQ_LineSource

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
  let we := cut.we
  let we1 := cut.we1
  let we2 := cut.we2
  let h0 := cut.h0
  let we3 := cut.we3
  let we4 := cut.we4
  let m := cut.m
  let h2 := cut.h2
  let we5 := cut.we5
  let m1 := cut.m1
  let c0 := cut.c0
  let we6 := cut.we6
  let m2 := cut.m2
  let c1 := cut.c1
  let we7 := cut.we7
  let h1 := cut.h1
  let we8 := cut.we8
  let m3 := cut.m3
  let h3 := cut.h3
  let we9 := cut.we9
  let we10 := cut.we10
  let we11 := cut.we11
  let we12 := cut.we12
  let we13 := cut.we13
  have Hwe := cut.Hwe
  have Hwe1 := cut.Hwe1
  have Hwe2 := cut.Hwe2
  have Hh0 := cut.Hh0
  have Hwe3 := cut.Hwe3
  have Hwe4 := cut.Hwe4
  have Hm := cut.Hm
  have Hh2 := cut.Hh2
  have Hwe5 := cut.Hwe5
  have Hm1 := cut.Hm1
  have Hc0 := cut.Hc0
  have Hwe6 := cut.Hwe6
  have Hm2 := cut.Hm2
  have Hc1 := cut.Hc1
  have Hwe7 := cut.Hwe7
  have Hh1 := cut.Hh1
  have Hwe8 := cut.Hwe8
  have Hm3 := cut.Hm3
  have Hh3 := cut.Hh3
  have Hwe9 := cut.Hwe9
  have Hwe10 := cut.Hwe10
  have Hwe11 := cut.Hwe11
  have Hwe12 := cut.Hwe12
  have Hwe13 := cut.Hwe13
  have h := cut.Hout
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
  refine SAQ_LineAlgebra.compose (decodeWide alpha) (decodeWide a) (decodeWide b)
    (decodeWide c) (decodeWide d) (decodeBase lx) (decodeBase ly) (decodeBase lz)
    (decodeWide h0) (decodeWide h1) (decodeWide h2) (decodeWide h3) (decodeWide out)
    ?_ ?_ ?_ ?_ Eout
  · simpa only [decodeQuarter] using Eh0
  · simpa only [decodeHalf] using Eh1
  · simpa only [decodeQuarter] using Eh2
  · simpa only [decodeHalf] using Eh3

#print axioms on_cuts
end AspisR1.SAQ_LineMeaning
end
