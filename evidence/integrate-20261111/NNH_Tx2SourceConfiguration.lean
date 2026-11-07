import NNH_Tx2Configuration
import NNH_EmitModel
import NJJ_QueryOps
import NJJ_Common
set_option autoImplicit false
noncomputable section
namespace NNH_Tx2SourceConfiguration
open Aeneas Aeneas.Std AspisR1 AdapterRw

def stage (base : VTop_Stages.Ops) : VTop_Stages.Ops :=
 NHT_Tx2CommonModel.constants {base with op2:=NJC_ClosedCalls.inactive,op13:=NHV_ReleaseOps.mark}

/-- Concrete runtime-value and emit projections of the existing LIBB source.
The separate physical runtime association is still required by the host. -/
def adapter (base : Ops) (env : RSL.Env) : Ops :=
 {base with op42:=fun _=>.ok (),op43:=fun _ parts=>LIB_Env.hashv env parts,op53:=NNH_EmitModel.code}

def fill (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env) :
 IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE :=
 {missing with adapter:=adapter missing.adapter env,stageBase:=stage missing.stageBase,query:=NJJ_QueryOps.concrete,geometry:=NFN_NEW_GeometryDictionary.adopted}

def configuration (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2Configuration.configuration (fill missing env) env err reserve

def sdk (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :=
 NNH_Tx2Configuration.sdk (fill missing env) env err reserve

theorem emit (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation) :
 (sdk missing env err reserve).op53=NNH_EmitModel.code := rfl

theorem hashv (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (parts : Slice (Slice U8)) :
 (sdk missing env err reserve).op43 () parts=LIB_Env.hashv env parts := rfl
#print axioms emit
#print axioms hashv
end NNH_Tx2SourceConfiguration
