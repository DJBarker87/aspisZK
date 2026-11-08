import NNV_GeometrySelectedStd
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryEq
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody
open NNH_Run5bGeometrySlots NNV_GeometrySelectedStd

theorem installed {C : Type} (base : Ops C) (x y : U32) :
 (Port5Q1_GeometryTerminal.install base).op5 x y = .ok (decide (x=y)) := rfl

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (x y : U32) :
 (ops m env err r).op5 x y = canonical.op5 x y :=
 (installed (base m env err r) x y).trans (installed cbase x y).symm
#print axioms installed
#print axioms source
end AspisR1.NNV_GeometryEq
end
