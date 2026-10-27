import RPu_FJf_RawResidue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_RawTower
open FJf_RawResidue (F)

abbrev C := QuadraticAlgebra F (-1) 0
abbrev Q := QuadraticAlgebra C (⟨2,1⟩ : C) 0

theorem carrier : Q=OraclePortCheckpointAbiC5.K := rfl

def pack (a b c d : F) : Q := ⟨⟨a,b⟩,⟨c,d⟩⟩

theorem multiply (a b c d e f g h : F) :
    pack (a*e-b*f+2*(c*g-d*h)-(c*h+d*g))
      (a*f+b*e+(c*g-d*h)+2*(c*h+d*g))
      (a*g+c*e-b*h-d*f) (a*h+b*g+c*f+d*e)=
    pack a b c d*pack e f g h := by
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;>
    simp only [pack,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,zero_mul,zero_add,add_zero,one_mul] <;> ring
#print axioms carrier
#print axioms multiply
end AspisR1.FJf_RawTower
end
