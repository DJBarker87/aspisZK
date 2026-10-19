import AspisFormal.CircleGroupOrder
import R17TableBasePowerBridge

set_option autoImplicit false

namespace R17CircleCoordinateMulBridge

/-- Coordinates of a maintained circle point in the residue bridge model. -/
def circleCoords (x : AspisCircleGroupOrder.C) :
    R17TableBasePowerBridge.ZC := ⟨x.1.1, x.1.2⟩

/-- The residue-model multiplication is exactly the coordinate projection of
maintained circle-group multiplication. -/
theorem zMul_circleCoords (x y : AspisCircleGroupOrder.C) :
    R17TableBasePowerBridge.zMul (circleCoords x) (circleCoords y) =
      circleCoords (x * y) := by
  apply R17TableBasePowerBridge.ZC.ext
  · simp [R17TableBasePowerBridge.zMul, circleCoords,
      AspisCircleGroupOrder.mul_re]
  · simp [R17TableBasePowerBridge.zMul, circleCoords,
      AspisCircleGroupOrder.mul_im]

#print axioms zMul_circleCoords

end R17CircleCoordinateMulBridge
