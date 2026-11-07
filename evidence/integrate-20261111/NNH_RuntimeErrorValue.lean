import NNH_Tx2StdConfiguration
set_option autoImplicit false
noncomputable section
namespace NNH_RuntimeErrorValue
open Aeneas Aeneas.Std AspisR1 AdapterRw
/-- Value of programs/r1-cost-probe/src/lib.rs:40. Its debug/log effects stay
with the existing RSL error event; this SDK slot has only a returned value. -/
def error (_ : aspis_r1_cost_probe.verifier.Error) : Result solana_program_error.ProgramError :=
 .ok .InvalidInstructionData

def residual (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) :
 IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE :=
 {missing with adapter:={missing.adapter with op44:=error}}

def configuration (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2StdConfiguration.configuration (residual missing) env err reserve

def sdk (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2StdConfiguration.sdk (residual missing) env err reserve

theorem selected (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :
 (sdk missing env err reserve).op44=error := rfl
#print axioms selected
end NNH_RuntimeErrorValue
