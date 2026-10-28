import NDO_JHl_Z0Square
import NDO_JFu_CircleExact
import RPt_JFq_Z0
import RPt_JFq_Z1
import RPt_JFq_Z2
import RPt_JFq_Z3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Z0X
open AspisV8R15.ExactTowerBase
def value : QM31Exact := ⟨⟨1922285720,1764102919⟩,⟨1090219375,1966128958⟩⟩
theorem source : value*JHl_Z0Square.denominator=(1 : QM31Exact)-JHl_Z0Square.square := by
  change (⟨⟨1922285720,1764102919⟩,⟨1090219375,1966128958⟩⟩ : QM31Exact)*⟨⟨763643100,790983522⟩,⟨1381251618,1287072416⟩⟩=(1 : QM31Exact)-⟨⟨763643099,790983522⟩,⟨1381251618,1287072416⟩⟩
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
end AspisR1.JHl_Z0X
end
