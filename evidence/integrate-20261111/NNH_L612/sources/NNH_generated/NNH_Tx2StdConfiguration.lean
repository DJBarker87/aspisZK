import NNH_AdapterStd
set_option autoImplicit false
noncomputable section
namespace NNH_Tx2StdConfiguration
open Aeneas Aeneas.Std AspisR1 AdapterRw

def residual (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) :
 IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE :=
 {missing with adapter:=NNH_AdapterStd.install missing.adapter}

def configuration (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2SourceConfiguration.configuration (residual missing) env err reserve

def sdk (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2SourceConfiguration.sdk (residual missing) env err reserve

theorem optionEq (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :
 @(sdk missing env err reserve).op2=@NNH_AdapterStd.optionEq := rfl

theorem fullIndex (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 {T : Type} (range : core.ops.range.RangeFull) (bytes : Slice T) :
 (sdk missing env err reserve).op4 range bytes=.ok bytes := rfl
#print axioms optionEq
#print axioms fullIndex
end NNH_Tx2StdConfiguration
