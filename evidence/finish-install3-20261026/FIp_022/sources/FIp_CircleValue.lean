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
  rcases cut with ⟨we,we1,we2,h0,we3,we4,we5,m,h1,we6,we7,m1,h2,we8,we9,m2,h3,we10,we11,we12,we13,we14,Hwe,Hwe1,Hwe2,Hh0,Hwe3,Hwe4,Hwe5,Hm,Hh1,Hwe6,Hwe7,Hm1,Hh2,Hwe8,Hwe9,Hm2,Hh3,Hwe10,Hwe11,Hwe12,Hwe13,Hwe14,run⟩
  constructor
  · exact (wide_add_success h0 we14 out (scale we2 h0 quarter Hh0).1
      (SAQ_RawWide.mul_exact alpha we13 we14 Hwe14).1 run).1
  · have e := SAQ_RawWide.add_exact h0 we14 out run
    rw [(SAQ_RawWide.mul_exact alpha we13 we14 Hwe14).2,
      SAQ_RawWide.add_exact h1 we12 we13 Hwe13,
      (SAQ_RawWide.mul_exact alpha we11 we12 Hwe12).2,
      SAQ_RawWide.add_exact h2 we10 we11 Hwe11,
      (SAQ_RawWide.mul_exact alpha h3 we10 Hwe10).2,
      (scale we9 h3 m2 Hh3).2,
      (baseMul m1 iy m2 Hm2).2,
      SAQ_RawWide.sub_exact we8 d we9 Hwe9,
      SAQ_RawWide.add_exact we3 c we8 Hwe8,
      (scale we7 h2 m1 Hh2).2,
      (baseMul SAQ_LineSource.quarter ix m1 Hm1).2,
      SAQ_RawWide.sub_exact we6 d we7 Hwe7,
      SAQ_RawWide.sub_exact we c we6 Hwe6,
      (scale we5 h1 m Hh1).2,
      (baseMul SAQ_LineSource.quarter iy m Hm).2,
      SAQ_RawWide.add_exact we4 d we5 Hwe5,
      SAQ_RawWide.sub_exact we3 c we4 Hwe4,
      SAQ_RawWide.sub_exact a b we3 Hwe3,
      (scale we2 h0 SAQ_LineSource.quarter Hh0).2,
      SAQ_RawWide.add_exact we1 d we2 Hwe2,
      SAQ_RawWide.add_exact we c we1 Hwe1,
      SAQ_RawWide.add_exact a b we Hwe] at e
    with_reducible exact e

#print axioms on_cuts
end AspisR1.FIp_CircleValue
end
