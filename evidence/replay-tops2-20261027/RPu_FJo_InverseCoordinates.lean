import RPu_FJo_GeometryCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_InverseCoordinates
open AspisWide.FinalEncoder
open AspisCircleGroupOrder
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod P) E]
theorem x (u : Fin 262144) :
    algebraMap (ZMod P) E (((Port5Q1_Domain.words u.val)[0]?.getD 0)⁻¹)=(exactCircleX u)⁻¹ := by
  rw [map_inv₀,FJo_GeometryCoordinates.x]
theorem y (u : Fin 262144) :
    algebraMap (ZMod P) E (((Port5Q1_Domain.words u.val)[1]?.getD 0)⁻¹)=(exactCircleY u)⁻¹ := by
  rw [map_inv₀,FJo_GeometryCoordinates.y]
#print axioms x
#print axioms y
end AspisR1.FJo_InverseCoordinates
end
