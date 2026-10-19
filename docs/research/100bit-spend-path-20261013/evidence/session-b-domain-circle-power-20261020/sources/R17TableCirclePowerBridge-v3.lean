import AspisFormal.CircleGroupOrder
import R17TableBasePowerBridge
import R17TableAChunk00Certificate
import R17TableExponentDomainBridge
import R17CircleCoordinatePowerBridge

set_option autoImplicit false

namespace R17TableCirclePowerBridge

open AspisCircleGroupOrder

def circleCoords (x : AspisCircleGroupOrder.C) :
    R17TableBasePowerBridge.ZC :=
  R17CircleCoordinateMulBridge.circleCoords x

theorem residueGenerator_eq_circleGenerator :
    R17TableBasePowerBridge.decode
        (R17TableAChunk00Certificate.toNatC
          R17TableBasePowerProbe.gen) = circleCoords AspisCircleGroupOrder.g := by
  apply R17TableBasePowerBridge.ZC.ext
  · norm_num [R17TableBasePowerBridge.decode,
      R17TableAChunk00Certificate.toNatC,
      R17TableBasePowerProbe.gen,
      circleCoords, R17CircleCoordinateMulBridge.circleCoords,
      AspisCircleGroupOrder.g, R17TableBasePowerBridge.P,
      AspisCircleGroupOrder.P]
  · norm_num [R17TableBasePowerBridge.decode,
      R17TableAChunk00Certificate.toNatC,
      R17TableBasePowerProbe.gen,
      circleCoords, R17CircleCoordinateMulBridge.circleCoords,
      AspisCircleGroupOrder.g, R17TableBasePowerBridge.P,
      AspisCircleGroupOrder.P]

theorem residuePower_eq_circlePower (n : Nat) :
    R17TableBasePowerBridge.zPow
        (R17TableBasePowerBridge.decode
          (R17TableAChunk00Certificate.toNatC
            R17TableBasePowerProbe.gen)) n =
      circleCoords (AspisCircleGroupOrder.g ^ n) := by
  rw [residueGenerator_eq_circleGenerator]
  exact R17CircleCoordinatePowerBridge.zPow_circleCoords
    AspisCircleGroupOrder.g n

theorem A00_entry_00_is_circle_power :
    circleCoords (AspisCircleGroupOrder.g ^
      R17TableExponentDomainBridge.leftExponent 0) =
      ⟨1022251061, 788094511⟩ := by
  have h := R17TableAChunk00Certificate.entry_00_zPow
  change R17TableBasePowerBridge.decode
      (R17TableAChunk00Certificate.toNatC
        (⟨1022251061, 788094511⟩ : R17TableBasePowerProbe.C)) =
    R17TableBasePowerBridge.zPow
      (R17TableBasePowerBridge.decode
        (R17TableAChunk00Certificate.toNatC
          R17TableBasePowerProbe.gen))
      (R17TableExponentDomainBridge.leftExponent 0) at h
  rw [residuePower_eq_circlePower] at h
  exact h.symm

#print axioms residueGenerator_eq_circleGenerator
#print axioms residuePower_eq_circlePower
#print axioms A00_entry_00_is_circle_power

end R17TableCirclePowerBridge
