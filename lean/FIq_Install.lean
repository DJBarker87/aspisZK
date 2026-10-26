import FIq_Terminal
import FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIq_Install
open DrvC_Installation

def seed {C : Type} (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  {c with boundaries:=FIq_Terminal.install c.boundaries}
def select {C : Type} (r : NP6_StdModel.Reservation) (c : Configuration FIo_Install.W C) :=
  FIp_Install.select r (seed c)
def boundaries (b : FIp_SemanticArithmetic.B) := FIp_Install.boundaries (FIq_Terminal.install b)
def configuration {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) := FIp_Install.configuration err (seed c) r

theorem terminal_fixed {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (configuration err c r).boundaries.terminal=FIq_Terminal.terminal := rfl

theorem seed_terminal_erased {C : Type} (c : Configuration FIo_Install.W C)
    (other : FIp_SemanticArithmetic.B) :
    seed {c with boundaries:={c.boundaries with terminal:=other.terminal}}=seed c := rfl

#print axioms terminal_fixed
#print axioms seed_terminal_erased
end AspisR1.FIq_Install
