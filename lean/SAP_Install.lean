import DrvC_FirstConstants
import F3M_CircleSource
import F3Q_CircleScope
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_Install
open DrvC_Installation

/-- Specialize the sole remaining semantic circle slot to its source wrapper.
The extraction association must mention this dictionary, not its free seed. -/
def configuration {F C : Type} (c : Configuration F C) : Configuration F C :=
  DrvC_FirstConstants.configuration {c with boundaries:=F3M_CircleSource.install c.boundaries}

theorem circle {F C : Type} (c : Configuration F C) :
    (configuration c).boundaries.circle=F3M_CircleSource.source := rfl

theorem boundaries {F C : Type} (c : Configuration F C) :
    (configuration c).boundaries=F3M_CircleSource.install c.boundaries := rfl

theorem unchanged_if_installed {F C : Type} (c : Configuration F C)
    (installed : c.boundaries.circle=F3M_CircleSource.source) :
    configuration c=DrvC_FirstConstants.configuration c := by
  unfold configuration
  rw [F3Q_CircleScope.install_eq c.boundaries installed]

#print axioms circle
#print axioms boundaries
#print axioms unchanged_if_installed
end AspisR1.SAP_Install
end
