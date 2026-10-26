import FIp_CircleCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_CircleValue
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof
open SAQ_LineSource

def formula (alpha a b c d : AspisWideTower.WideExact) (ix iy : FP) :=
  let embed := algebraMap FP AspisWideTower.WideExact
  let h0 := (a+b+c+d)*embed R1ZCircleFoldMathV1.rustQuarter
  let h1 := (a-b-c+d)*embed (R1ZCircleFoldMathV1.rustQuarter*iy)
  let h2 := (a+b-c-d)*embed (R1ZCircleFoldMathV1.rustQuarter*ix)
  let h3 := (a-b+c-d)*embed (R1ZCircleFoldMathV1.rustQuarter*ix*iy)
  h0+alpha*(h1+alpha*(h2+alpha*h3))

theorem on_cuts (alpha a b c d out : E) (ix iy : U32)
    (cut : FIp_CircleCuts.Cuts alpha a b c d ix iy out) :
    CanonicalWide out ∧ decodeWide out=formula (decodeWide alpha)
      (decodeWide a) (decodeWide b) (decodeWide c) (decodeWide d) (decodeBase ix) (decodeBase iy) := by
  have e0 := (scale cut.we2 cut.h0 quarter cut.Hh0).2
  rw [SAQ_RawWide.add_exact cut.we1 d cut.we2 cut.Hwe2,
    SAQ_RawWide.add_exact cut.we c cut.we1 cut.Hwe1,
    SAQ_RawWide.add_exact a b cut.we cut.Hwe] at e0
  have e1 := (scale cut.we5 cut.h1 cut.m cut.Hh1).2
  rw [(baseMul quarter iy cut.m cut.Hm).2,
    SAQ_RawWide.add_exact cut.we4 d cut.we5 cut.Hwe5,
    SAQ_RawWide.sub_exact cut.we3 c cut.we4 cut.Hwe4,
    SAQ_RawWide.sub_exact a b cut.we3 cut.Hwe3] at e1
  have e2 := (scale cut.we7 cut.h2 cut.m1 cut.Hh2).2
  rw [(baseMul quarter ix cut.m1 cut.Hm1).2,
    SAQ_RawWide.sub_exact cut.we6 d cut.we7 cut.Hwe7,
    SAQ_RawWide.sub_exact cut.we c cut.we6 cut.Hwe6,
    SAQ_RawWide.add_exact a b cut.we cut.Hwe] at e2
  have e3 := (scale cut.we9 cut.h3 cut.m2 cut.Hh3).2
  rw [(baseMul cut.m1 iy cut.m2 cut.Hm2).2,
    (baseMul quarter ix cut.m1 cut.Hm1).2,
    SAQ_RawWide.sub_exact cut.we8 d cut.we9 cut.Hwe9,
    SAQ_RawWide.add_exact cut.we3 c cut.we8 cut.Hwe8,
    SAQ_RawWide.sub_exact a b cut.we3 cut.Hwe3] at e3
  have e := SAQ_RawWide.add_exact cut.h0 cut.we14 out cut.Hout
  rw [(SAQ_RawWide.mul_exact alpha cut.we13 cut.we14 cut.Hwe14).2,
    SAQ_RawWide.add_exact cut.h1 cut.we12 cut.we13 cut.Hwe13,
    (SAQ_RawWide.mul_exact alpha cut.we11 cut.we12 cut.Hwe12).2,
    SAQ_RawWide.add_exact cut.h2 cut.we10 cut.we11 cut.Hwe11,
    (SAQ_RawWide.mul_exact alpha cut.h3 cut.we10 cut.Hwe10).2,e0,e1,e2,e3] at e
  constructor
  · exact (wide_add_success cut.h0 cut.we14 out
      (scale cut.we2 cut.h0 quarter cut.Hh0).1
      (SAQ_RawWide.mul_exact alpha cut.we13 cut.we14 cut.Hwe14).1 cut.Hout).1
  · with_reducible exact e

#print axioms on_cuts
end AspisR1.FIp_CircleValue
end
