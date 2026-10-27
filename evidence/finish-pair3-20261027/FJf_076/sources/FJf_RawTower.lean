import FJf_RawResidue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_RawTower
open FJf_RawResidue (F)

def pack (a b c d : F) : OraclePortCheckpointAbiC5.K := ⟨⟨a,b⟩,⟨c,d⟩⟩

theorem multiply (a b c d e f g h : F) :
    pack (a*e-b*f+2*(c*g-d*h)-(c*h+d*g))
      (a*f+b*e+(c*g-d*h)+2*(c*h+d*g))
      (a*g+c*e-b*h-d*f) (a*h+b*g+c*f+d*e)=
    pack a b c d*pack e f g h := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · change a*e-b*f+2*(c*g-d*h)-(c*h+d*g)=
        (a*e+(-1)*b*f)+(2*(c*g+(-1)*d*h)+(-1)*(c*h+d*g))
      ring
    · change a*f+b*e+(c*g-d*h)+2*(c*h+d*g)=
        (a*f+b*e+0*b*f)+(2*(c*h+d*g+0*d*h)+(c*g+(-1)*d*h)+0*(c*h+d*g+0*d*h))
      ring
  · apply QuadraticAlgebra.ext
    · change a*g+c*e-b*h-d*f=
        (a*g+(-1)*b*h)+(c*e+(-1)*d*f)+0
      ring
    · change a*h+b*g+c*f+d*e=
        (a*h+b*g+0*b*h)+(c*f+d*e+0*d*f)+0
      ring
#print axioms multiply
end AspisR1.FJf_RawTower
end
