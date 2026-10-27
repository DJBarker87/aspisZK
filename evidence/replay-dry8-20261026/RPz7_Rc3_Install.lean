import RPz7_Rc2_Install
import RPz7_SAP_Install
import RPz7_SAP_ConfigScope
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc3_Install
open DrvC_Installation

def select {F C : Type} (c : Configuration F C) (r : NP6_StdModel.Reservation) :=
  {Rc2_Install.select c r with boundaries := F3M_CircleSource.install c.boundaries}

def configuration {F C : Type} (c : Configuration F C) (r : NP6_StdModel.Reservation) :=
  SAP_Install.configuration (Rc2_Install.select c r)

theorem compatible {F C : Type} (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration c r = Rc2_Install.configuration
      {c with boundaries := F3M_CircleSource.install c.boundaries} r := rfl

theorem sap {F C : Type} (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration c r = SAP_Install.configuration (Rc2_Install.select c r) := rfl

theorem standard {F C : Type} (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    (configuration c r).std = NP6_StdModel.calls r := rfl

theorem circle {F C : Type} (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    (configuration c r).boundaries = F3M_CircleSource.install c.boundaries := rfl

theorem exact_scope {F C : Type} (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    configuration c r = Rc2_Install.configuration c r ↔
      c.boundaries.circle = F3M_CircleSource.source :=
  SAP_ConfigScope.exact_scope (Rc2_Install.select c r)

theorem dictionary {F C : Type} (c : Configuration F C) (r : NP6_StdModel.Reservation) :
    sdk (configuration c r) = SdkD_PairBatches.dictionary
      (configuration c r).adapter (configuration c r).currentBase
      (configuration c r).stageBase (configuration c r).finish
      (configuration c r).reserved (configuration c r).query
      (configuration c r).geometry (configuration c r).boundaries
      (NP6_StdModel.calls r) := DrvC_Installation.aus1_dictionary _

#print axioms compatible
#print axioms sap
#print axioms standard
#print axioms circle
#print axioms exact_scope
#print axioms dictionary
end AspisR1.Rc3_Install
end
