import NHW_QueryIdentity
import NGK_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_DeployedQuery
open Aeneas Aeneas.Std Result
abbrev configuration {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (reservation : NP6_StdModel.Reservation) :=
 FIp_Install.configuration err (IDa_Deployed.deployedConfiguration missing err reservation) reservation
/-- The counterexample for arbitrary Configuration.query is excluded by the
headline's concrete SAQ decoder/line installation. -/
theorem line {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) :
 (Tx1Q_QueryBridge.leaves (configuration missing err r).query).op16=SAQ_LineQuery.line := rfl

theorem dots {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) :
 (Tx1Q_QueryBridge.leaves (configuration missing err r).query).op20=FIp_DotsAdapter.dots := rfl

theorem add {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) :
 (Tx1Q_QueryBridge.leaves (configuration missing err r).query).op2=SAQ_Arithmetic.add := rfl

theorem product {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) :
 (Tx1Q_QueryBridge.leaves (configuration missing err r).query).op3=SAQ_MixedSource.mulE := rfl

theorem power {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) :
 (Tx1Q_QueryBridge.leaves (configuration missing err r).query).op9=SAQ_Arithmetic.mulK := rfl
#print axioms line
#print axioms dots
#print axioms add
#print axioms product
#print axioms power
end AspisR1.NHW_DeployedQuery
