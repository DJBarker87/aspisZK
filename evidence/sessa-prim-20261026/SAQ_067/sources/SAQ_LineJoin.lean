import SAQ_LineChannels
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineJoin
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide AspisR1CurrentWide.Proof SAQ_LineSource SAQ_LineChannels
variable (alpha a b c d out : E) (lx ly lz : U32)
theorem on_cuts (cut : Cuts alpha a b c d lx ly lz out) : CanonicalWide out ∧ decodeWide out =
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

#print axioms on_cuts
#check @SAQ_LineChannels.h0
#check @SAQ_LineChannels.h1
set_option pp.explicit true in
#print SAQ_LineChannels.h0
end AspisR1.SAQ_LineJoin
end
