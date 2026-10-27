import Rc3_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_ViewPins
open Aeneas Aeneas.Std Result

theorem constants {F C : Type} (c : DrvC_Installation.Configuration F C)
    (r : NP6_StdModel.Reservation) :
    let ops := DrvC_Installation.stage (Rc3_Install.configuration c r)
    ops.op22 = ok 7527#usize ∧ ops.op15 = ok 7751#usize ∧
    ops.op14 = ok 7783#usize ∧ ops.op21 = ok 8007#usize ∧ ops.op20 = ok 10055#usize :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms constants
end AspisR1.SAG_ViewPins
end
