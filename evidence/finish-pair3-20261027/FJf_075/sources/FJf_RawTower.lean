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
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp only [pack,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      AspisV8R15.ExactTowerBase.qm31R] <;> ring
#print axioms multiply
end AspisR1.FJf_RawTower
end
