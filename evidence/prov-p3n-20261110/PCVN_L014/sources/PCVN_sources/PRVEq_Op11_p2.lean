-- PCVN_ item (1) op11: the deployed geometry slot at the deployed dictionary NFN_NEW_GeometryDictionary.adopted.
import Aeneas
import PRVEq_Tx2Deployed_n0
import NJC_ClosedCalls
import NJJ_QueryOps
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace PCVN_Op11
open AspisR1 PCVN_Tx2Deployed

theorem install_adopted : Port5Q1_GeometryTerminal.install NFN_NEW_GeometryDictionary.adopted = NFN_NEW_GeometryDictionary.adopted := by
  rfl
end PCVN_Op11
#print axioms PCVN_Op11.install_adopted
