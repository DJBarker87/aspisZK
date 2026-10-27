import RPz7_Rc5_Install
import RPz7_SAP_Binding
import SAQ_Constructor
import RPz7_F3X_Installation
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Y_InstalledLaws
open Aeneas Aeneas.Std Result DrvC_Installation

theorem configuration {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) :
    F3V_Install.configuration (Rc2_Install.configuration (Rc5_Install.seed err c) r) =
      Rc5_Install.configuration err c r := rfl

theorem prepare {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) :
    let a := Rc5_Install.configuration err c r
    WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current a.currentBase) a.reserved a.query
        a.geometry a.boundaries a.std) :=
  SAP_Binding.prepare (Rc2_Install.select (Rc5_Install.seed err c) r)

theorem primitives {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) :
    Port5Q1_QueryPorts.SessionAPrimitives (Rc5_Install.configuration err c r).query :=
  SAQ_Decoder.primitives c.query

theorem canonical {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (Rc5_Install.configuration err c r).geometry :=
  SAQ_Constructor.canonical err c.geometry

theorem domain {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) :
    Port5Q1_Domain.SessionADomain (Rc5_Install.configuration err c r).geometry :=
  SAQ_Constructor.domain err c.geometry

theorem multiply {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) :
    (Rc5_Install.configuration err c r).geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := rfl

theorem one {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) :
    (Rc5_Install.configuration err c r).geometry.op7=ok (1#u32) := rfl

theorem inverse {F C : Type} (err : C) (c : Configuration F C)
    (r : NP6_StdModel.Reservation) :
    (Rc5_Install.configuration err c r).geometry.op11=Port4C_InverseExecution.inverse_owned :=
  SAQ_Constructor.inverse err c.geometry

#print axioms configuration
#print axioms prepare
#print axioms primitives
#print axioms canonical
#print axioms domain
#print axioms multiply
#print axioms one
#print axioms inverse
end AspisR1.F3Y_InstalledLaws
end
