import Rc5_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc6_Install
open DrvC_Installation
/-- Rc6 keeps every Rc5 dictionary slot. PFin is re-derived at this instance. -/
theorem parser_base {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    Rc5_Install.configuration err c r = Rc2_Install.configuration
      {Rc5_Install.seed err c with boundaries := F3M_CircleSource.install c.boundaries} r := rfl
/-- The P6 accepted-run refinement and Rc5 have the same dictionary. -/
theorem p6_base {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    Rc5_Install.configuration err c r = Rc3_Install.configuration (Rc5_Install.seed err c) r := rfl
/-- Reconstructing the instance at the generic same-cuts boundary preserves all fields. -/
theorem reconstruct {F C : Type} (err : C) (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    (⟨(Rc5_Install.configuration err c r).adapter,(Rc5_Install.configuration err c r).currentBase,
      (Rc5_Install.configuration err c r).stageBase,(Rc5_Install.configuration err c r).finish,
      (Rc5_Install.configuration err c r).reserved,(Rc5_Install.configuration err c r).query,
      (Rc5_Install.configuration err c r).geometry,F3M_CircleSource.install c.boundaries,
      NP6_StdModel.calls r⟩ : Configuration F C) = Rc5_Install.configuration err c r := rfl
#print axioms parser_base
#print axioms p6_base
#print axioms reconstruct
end AspisR1.Rc6_Install
end
