import NDO_JHl_Z0Square
import NDO_JFu_CircleExact
import RPt_JFq_Z0
import RPt_JFq_Z1
import RPt_JFq_Z2
import RPt_JFq_Z3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Z0Y
open AspisV8R15.ExactTowerBase
def value : QM31Exact := ⟨⟨581146816,250060454⟩,⟨1903115135,1815951825⟩⟩
theorem source : value*JHl_Z0Square.denominator=2*JFu_CircleParameters.t25 := by
  change (⟨⟨581146816,250060454⟩,⟨1903115135,1815951825⟩⟩ : QM31Exact)*⟨⟨763643100,790983522⟩,⟨1381251618,1287072416⟩⟩=(2 : QM31Exact)*⟨⟨816245010,114551508⟩,⟨1501205590,2011200735⟩⟩
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
end AspisR1.JHl_Z0Y
end
