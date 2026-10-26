import RPz7_SAP_PrepareOwner
import RPz7_SAP_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_Binding
open DrvC_Installation

theorem prepare {F C : Type} (c : Configuration F C) :
    WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (SAP_Install.configuration c).currentBase)
        (SAP_Install.configuration c).reserved (SAP_Install.configuration c).query
        (SAP_Install.configuration c).geometry (SAP_Install.configuration c).boundaries
        (SAP_Install.configuration c).std) :=
  SAP_PrepareOwner.installed
    (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base
      (Op5T_Concrete.current (SAP_Install.configuration c).currentBase)
      (SAP_Install.configuration c).reserved (SAP_Install.configuration c).query
      (SAP_Install.configuration c).geometry))) c.boundaries (SAP_Install.configuration c).std

#print axioms prepare
end AspisR1.SAP_Binding
end
