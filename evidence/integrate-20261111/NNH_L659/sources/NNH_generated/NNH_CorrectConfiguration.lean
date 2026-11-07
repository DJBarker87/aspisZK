import NNH_AdapterStdCorrect
import NNH_RuntimeErrorValue
set_option autoImplicit false
noncomputable section
namespace NNH_CorrectConfiguration
open Aeneas Aeneas.Std AspisR1 AdapterRw

def residual (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env) :=
 NNH_Tx2SourceConfiguration.fill
 {missing with adapter:=NNH_AdapterStdCorrect.install {missing.adapter with
  op19:=.ok 1520#usize,op44:=NNH_RuntimeErrorValue.error}} env

def configuration (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2Configuration.configuration (residual missing env) env err reserve

def sdk (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2Configuration.sdk (residual missing env) env err reserve

theorem stage (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :
 DrvC_Installation.stage (configuration missing env err reserve)=
 DrvC_Installation.stage (NNH_RuntimeErrorValue.configuration missing env err reserve) := rfl

#print axioms stage
end NNH_CorrectConfiguration
