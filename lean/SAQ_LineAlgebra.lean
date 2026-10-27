import SAQ_LineSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineAlgebra
open SAQ_LineSource
abbrev FP := ZMod AspisCircleGroupOrder.P

theorem compose {K : Type} [Field K] [Algebra FP K]
    (alpha a b c d : K) (ix iy iz : FP) (h0 h1 h2 h3 out : K)
    (e0 : h0=(a+b+c+d)*algebraMap FP K R1ZCircleFoldMathV1.rustQuarter)
    (e1 : h1=((a-b)*algebraMap FP K (R1ZCircleFoldMathV1.rustHalf*ix)+
      (d-c)*algebraMap FP K (R1ZCircleFoldMathV1.rustHalf*iy))*
      algebraMap FP K R1ZCircleFoldMathV1.rustHalf)
    (e2 : h2=(a+b-c-d)*algebraMap FP K (R1ZCircleFoldMathV1.rustQuarter*iz))
    (e3 : h3=((a-b)*algebraMap FP K (R1ZCircleFoldMathV1.rustHalf*ix)-
      (d-c)*algebraMap FP K (R1ZCircleFoldMathV1.rustHalf*iy))*
      algebraMap FP K (R1ZCircleFoldMathV1.rustHalf*iz))
    (horner : out=h0+alpha*(h1+alpha*(h2+alpha*h3))) :
    out=R1ZCircleFoldMathV1.sourceLineFold alpha (values4 a b c d) ix iy iz := by
  rw [horner,e0,e1,e2,e3]
  rfl

#print axioms compose
end AspisR1.SAQ_LineAlgebra
end
