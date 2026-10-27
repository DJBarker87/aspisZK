import SAQ_LineAlgebra
import SAQ_LineCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineChannels
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof SAQ_LineSource

variable (alpha a b c d out : E) (lx ly lz : U32)
variable (cut : Cuts alpha a b c d lx ly lz out)

theorem h0 : decodeWide cut.h0 = (decodeWide a+decodeWide b+decodeWide c+decodeWide d)*
    algebraMap FP AspisWideTower.WideExact R1ZCircleFoldMathV1.rustQuarter := by
  have e := (scale cut.we2 cut.h0 quarter cut.Hh0).2
  rw [SAQ_RawWide.add_exact cut.we1 d cut.we2 cut.Hwe2,
    SAQ_RawWide.add_exact cut.we c cut.we1 cut.Hwe1,
    SAQ_RawWide.add_exact a b cut.we cut.Hwe] at e
  exact e

theorem h2 : decodeWide cut.h2 = (decodeWide a+decodeWide b-decodeWide c-decodeWide d)*
    algebraMap FP AspisWideTower.WideExact (R1ZCircleFoldMathV1.rustQuarter*decodeBase lz) := by
  have e := (scale cut.we4 cut.h2 cut.m cut.Hh2).2
  have m := (baseMul quarter lz cut.m cut.Hm).2
  rw [m,SAQ_RawWide.sub_exact cut.we3 d cut.we4 cut.Hwe4,
    SAQ_RawWide.sub_exact cut.we c cut.we3 cut.Hwe3,
    SAQ_RawWide.add_exact a b cut.we cut.Hwe] at e
  exact e

theorem c0 : decodeWide cut.c0 = (decodeWide a-decodeWide b)*
    algebraMap FP AspisWideTower.WideExact (R1ZCircleFoldMathV1.rustHalf*decodeBase lx) := by
  have e := (scale cut.we5 cut.c0 cut.m1 cut.Hc0).2
  have m := (baseMul 1073741824#u32 lx cut.m1 cut.Hm1).2
  rw [m,SAQ_RawWide.sub_exact a b cut.we5 cut.Hwe5] at e
  exact e

theorem c1 : decodeWide cut.c1 = (decodeWide d-decodeWide c)*
    algebraMap FP AspisWideTower.WideExact (R1ZCircleFoldMathV1.rustHalf*decodeBase ly) := by
  have e := (scale cut.we6 cut.c1 cut.m2 cut.Hc1).2
  have m := (baseMul 1073741824#u32 ly cut.m2 cut.Hm2).2
  rw [m,SAQ_RawWide.sub_exact d c cut.we6 cut.Hwe6] at e
  exact e

theorem h1 : decodeWide cut.h1 = ((decodeWide a-decodeWide b)*
    algebraMap FP AspisWideTower.WideExact (R1ZCircleFoldMathV1.rustHalf*decodeBase lx)+
    (decodeWide d-decodeWide c)*
    algebraMap FP AspisWideTower.WideExact (R1ZCircleFoldMathV1.rustHalf*decodeBase ly))*
    algebraMap FP AspisWideTower.WideExact R1ZCircleFoldMathV1.rustHalf := by
  have e := (scale cut.we7 cut.h1 1073741824#u32 cut.Hh1).2
  rw [SAQ_RawWide.add_exact cut.c0 cut.c1 cut.we7 cut.Hwe7,
    c0 alpha a b c d out lx ly lz cut,c1 alpha a b c d out lx ly lz cut] at e
  exact e

theorem h3 : decodeWide cut.h3 = ((decodeWide a-decodeWide b)*
    algebraMap FP AspisWideTower.WideExact (R1ZCircleFoldMathV1.rustHalf*decodeBase lx)-
    (decodeWide d-decodeWide c)*
    algebraMap FP AspisWideTower.WideExact (R1ZCircleFoldMathV1.rustHalf*decodeBase ly))*
    algebraMap FP AspisWideTower.WideExact (R1ZCircleFoldMathV1.rustHalf*decodeBase lz) := by
  have e := (scale cut.we8 cut.h3 cut.m3 cut.Hh3).2
  have m := (baseMul 1073741824#u32 lz cut.m3 cut.Hm3).2
  rw [m,SAQ_RawWide.sub_exact cut.c0 cut.c1 cut.we8 cut.Hwe8,
    c0 alpha a b c d out lx ly lz cut,c1 alpha a b c d out lx ly lz cut] at e
  exact e

theorem horner : decodeWide out=decodeWide cut.h0+decodeWide alpha*
    (decodeWide cut.h1+decodeWide alpha*(decodeWide cut.h2+decodeWide alpha*decodeWide cut.h3)) := by
  have e := SAQ_RawWide.add_exact cut.h0 cut.we13 out cut.Hout
  rw [(SAQ_RawWide.mul_exact alpha cut.we12 cut.we13 cut.Hwe13).2,
    SAQ_RawWide.add_exact cut.h1 cut.we11 cut.we12 cut.Hwe12,
    (SAQ_RawWide.mul_exact alpha cut.we10 cut.we11 cut.Hwe11).2,
    SAQ_RawWide.add_exact cut.h2 cut.we9 cut.we10 cut.Hwe10,
    (SAQ_RawWide.mul_exact alpha cut.h3 cut.we9 cut.Hwe9).2] at e
  exact e

theorem on_cuts : CanonicalWide out ∧ decodeWide out =
    R1ZCircleFoldMathV1.sourceLineFold (decodeWide alpha)
      (values4 (decodeWide a) (decodeWide b) (decodeWide c) (decodeWide d))
      (decodeBase lx) (decodeBase ly) (decodeBase lz) := by
  refine ⟨SAQ_LineCanonical.on_cuts alpha a b c d out lx ly lz cut,?_⟩
  exact SAQ_LineAlgebra.compose (decodeWide alpha) (decodeWide a) (decodeWide b)
    (decodeWide c) (decodeWide d) (decodeBase lx) (decodeBase ly) (decodeBase lz)
    (decodeWide cut.h0) (decodeWide cut.h1) (decodeWide cut.h2) (decodeWide cut.h3) (decodeWide out)
    (h0 alpha a b c d out lx ly lz cut) (h1 alpha a b c d out lx ly lz cut)
    (h2 alpha a b c d out lx ly lz cut) (h3 alpha a b c d out lx ly lz cut)
    (horner alpha a b c d out lx ly lz cut)

#print axioms h0
#print axioms h2
#print axioms c0
#print axioms c1
#print axioms h1
#print axioms h3
#print axioms horner
#print axioms on_cuts
end AspisR1.SAQ_LineChannels
end
