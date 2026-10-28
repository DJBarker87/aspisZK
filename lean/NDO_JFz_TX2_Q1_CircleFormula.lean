import NDO_JFz_TX2_Q1_CircleCoefficients
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_CircleFormula
open Aeneas Aeneas.Std Result
open JFz_TX2_Q1_CircleNumbers JFz_TX2_Q1_CircleCoefficients

theorem scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
theorem ix : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 840707391=(840707391:FE) :=
  map_natCast _ _
theorem iy : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1785601017=(1785601017:FE) :=
  map_natCast _ _
theorem v0 : Port5Q1_OpeningValues.values JFz_TX2_Q1_Dots0.value 0=d0 := rfl
theorem v1 : Port5Q1_OpeningValues.values JFz_TX2_Q1_Dots0.value 1=d1 := rfl
theorem v2 : Port5Q1_OpeningValues.values JFz_TX2_Q1_Dots0.value 2=d2 := rfl
theorem v3 : Port5Q1_OpeningValues.values JFz_TX2_Q1_Dots0.value 3=d3 := rfl

theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 840707391)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1785601017)
    (Port5Q1_OpeningValues.values JFz_TX2_Q1_Dots0.value)=JFz_TX2_Q1_CircleNumbers.value := by
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
end AspisR1.JFz_TX2_Q1_CircleFormula
end
