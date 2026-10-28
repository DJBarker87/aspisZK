import NDO_JFu_CircleExact
import RPt_JFq_Z0
import RPt_JFq_Z1
import RPt_JFq_Z2
import RPt_JFq_Z3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Z1Square
open AspisV8R15.ExactTowerBase
def square : QM31Exact := ⟨⟨10478460,1524343433⟩,⟨1324550741,262831333⟩⟩
def denominator : QM31Exact := ⟨⟨10478461,1524343433⟩,⟨1324550741,262831333⟩⟩
theorem source : JFu_CircleParameters.t26^2=square := by
  rw [pow_two]
  change (⟨⟨758445278,139479390⟩,⟨789205686,1156709222⟩⟩ : QM31Exact)*⟨⟨758445278,139479390⟩,⟨789205686,1156709222⟩⟩=⟨⟨10478460,1524343433⟩,⟨1324550741,262831333⟩⟩
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
theorem den : 1+JFu_CircleParameters.t26^2=denominator := by
  rw [source]
  change (1 : QM31Exact)+⟨⟨10478460,1524343433⟩,⟨1324550741,262831333⟩⟩=⟨⟨10478461,1524343433⟩,⟨1324550741,262831333⟩⟩
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms den
end AspisR1.JHl_Z1Square
end
