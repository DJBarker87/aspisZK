import NDO_JHl_Z1Square
import NDO_JFu_CircleExact
import RPt_JFq_Z0
import RPt_JFq_Z1
import RPt_JFq_Z2
import RPt_JFq_Z3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Z1Y
open AspisV8R15.ExactTowerBase
def value : QM31Exact := ⟨⟨1362468980,298807548⟩,⟨913680565,2038915166⟩⟩
theorem source : value*JHl_Z1Square.denominator=2*JFu_CircleParameters.t26 := by
  change (⟨⟨1362468980,298807548⟩,⟨913680565,2038915166⟩⟩ : QM31Exact)*⟨⟨10478461,1524343433⟩,⟨1324550741,262831333⟩⟩=(2 : QM31Exact)*⟨⟨758445278,139479390⟩,⟨789205686,1156709222⟩⟩
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
end AspisR1.JHl_Z1Y
end
