import NNV_GeometryPrefix
import NNV_GeometrySelectedStd
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryPrefixSelected
open Aeneas Aeneas.Std Result NNH_Run5bGeometrySlots NNV_GeometrySelectedStd

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (s : Slice U32) :
 (ops m env err r).op13 s = canonical.op13 s :=
 NNV_GeometryPrefix.source (base m env err r) cbase
  (funext fun x => funext fun y => NNH_Run5bGeometrySlots.multiply m env err r x y)
  (NNH_Run5bGeometrySlots.one m env err r) s
#print axioms source
end AspisR1.NNV_GeometryPrefixSelected
end
