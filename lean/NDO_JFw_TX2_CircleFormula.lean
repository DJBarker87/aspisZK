import NDO_JFw_TX2_CircleCoefficients
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_CircleFormula
open Aeneas Aeneas.Std Result
open JFw_TX2_CircleNumbers JFw_TX2_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 243259912=(243259912:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1029545577=(1029545577:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFw_TX2_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFw_TX2_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFw_TX2_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFw_TX2_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 243259912)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1029545577)
    (Port5Q1_OpeningValues.values JFw_TX2_Dots0.value)=JFw_TX2_CircleNumbers.value := by
  rw [scalar,ix,iy]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms scalar
#print axioms ix
#print axioms iy
#print axioms v0
#print axioms v1
#print axioms v2
#print axioms v3
#print axioms formula
end AspisR1.JFw_TX2_CircleFormula
end
