import NNH_Stage2CallInputs
import NNH_Stage2Fission
set_option autoImplicit false
noncomputable section
namespace NNH_Stage2SourceConfiguration
open Aeneas Aeneas.Std AspisR1 AdapterRw
/-- Frozen late-public statement width, used by the original enclosing
statement-width constant. Residual data are still explicit. -/
def select (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) :=
 {missing with adapter:={missing.adapter with op19:=.ok 1520#usize}}
abbrev sdk (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_RuntimeErrorValue.sdk (select missing) env err reserve

theorem lateWidth (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :
 (sdk missing env err reserve).op19=.ok 1520#usize := rfl
#print axioms lateWidth
end NNH_Stage2SourceConfiguration
