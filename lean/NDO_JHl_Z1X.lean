import NDO_JHl_Z1Square
import NDO_JFu_CircleExact
import RPt_JFq_Z0
import RPt_JFq_Z1
import RPt_JFq_Z2
import RPt_JFq_Z3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Z1X
open AspisV8R15.ExactTowerBase
def value : QM31Exact := ⟨⟨1598687308,1705339602⟩,⟨50113148,396595219⟩⟩
theorem source : value*JHl_Z1Square.denominator=(1 : QM31Exact)-JHl_Z1Square.square := by
  change (⟨⟨1598687308,1705339602⟩,⟨50113148,396595219⟩⟩ : QM31Exact)*⟨⟨10478461,1524343433⟩,⟨1324550741,262831333⟩⟩=(1 : QM31Exact)-⟨⟨10478460,1524343433⟩,⟨1324550741,262831333⟩⟩
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
end AspisR1.JHl_Z1X
end
