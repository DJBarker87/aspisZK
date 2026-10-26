import Rc6_Install
import F3Y_InstalledLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc7_Install
open DrvC_Installation
/-- The headline and native pair use precisely the Rc6 dictionary. -/
theorem headline {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    F3V_Install.configuration (Rc2_Install.configuration (Rc5_Install.seed err c) r) =
      Rc5_Install.configuration err c r := rfl
/-- P2P's constructor reconstructs the same dictionary, including std slots. -/
theorem native {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    (⟨(Rc5_Install.configuration err c r).adapter,(Rc5_Install.configuration err c r).currentBase,
      (Rc5_Install.configuration err c r).stageBase,(Rc5_Install.configuration err c r).finish,
      (Rc5_Install.configuration err c r).reserved,(Rc5_Install.configuration err c r).query,
      (Rc5_Install.configuration err c r).geometry,F3M_CircleSource.install c.boundaries,
      NP6_StdModel.calls r⟩ : Configuration F C) = Rc5_Install.configuration err c r := rfl
#print axioms headline
#print axioms native
end AspisR1.Rc7_Install
end
