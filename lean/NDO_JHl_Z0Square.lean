import NDO_JFu_CircleExact
import RPt_JFq_Z0
import RPt_JFq_Z1
import RPt_JFq_Z2
import RPt_JFq_Z3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Z0Square
open AspisV8R15.ExactTowerBase
def square : QM31Exact := ⟨⟨763643099,790983522⟩,⟨1381251618,1287072416⟩⟩
def denominator : QM31Exact := ⟨⟨763643100,790983522⟩,⟨1381251618,1287072416⟩⟩
theorem source : JFu_CircleParameters.t25^2=square := by
  rw [pow_two]
  change (⟨⟨816245010,114551508⟩,⟨1501205590,2011200735⟩⟩ : QM31Exact)*⟨⟨816245010,114551508⟩,⟨1501205590,2011200735⟩⟩=⟨⟨763643099,790983522⟩,⟨1381251618,1287072416⟩⟩
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
theorem den : 1+JFu_CircleParameters.t25^2=denominator := by
  rw [source]
  change (1 : QM31Exact)+⟨⟨763643099,790983522⟩,⟨1381251618,1287072416⟩⟩=⟨⟨763643100,790983522⟩,⟨1381251618,1287072416⟩⟩
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms den
end AspisR1.JHl_Z0Square
end
