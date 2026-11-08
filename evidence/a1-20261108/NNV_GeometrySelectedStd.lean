import NNV_GeometryInstallSlots
import NNV_GeometryCallbacks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometrySelectedStd
open Aeneas Aeneas.Std Result NNH_Run5bGeometrySlots Port3_NativeGeometryBody
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
abbrev base := (NNH_CorrectConfiguration.configuration m env err r).geometry
abbrev cbase := NFN_NEB_ActualGeometryModel.install NFN_NEW_GeometryRawInterface.ops NFN_NEW_GeometryDictionary.err

theorem array : @(ops m env err r).op0 = @canonical.op0 :=
 (NNV_GeometryInstallSlots.array (base m env err r)).trans
  (NNV_GeometryInstallSlots.array cbase).symm

theorem iterator : @(ops m env err r).op1 = @canonical.op1 :=
 (NNV_GeometryInstallSlots.iterator (base m env err r)).trans
  (NNV_GeometryInstallSlots.iterator cbase).symm

theorem mapped : @(ops m env err r).mapIterator = @canonical.mapIterator :=
 (NNV_GeometryInstallSlots.mapped (base m env err r)).trans
  (NNV_GeometryInstallSlots.mapped cbase).symm

theorem empty (T : Type) (a : alloc.vec.Vec T) :
 (ops m env err r).op4 Global a = canonical.op4 Global a :=
 (NNV_GeometryInstallSlots.empty (base m env err r) T a).trans
  (NNV_GeometryInstallSlots.empty cbase T a).symm

theorem any {T F : Type} (pred : core.ops.function.FnMut F T Bool)
 (it : core.slice.iter.Iter T) (f : F) :
 (ops m env err r).op3 pred it f = canonical.op3 pred it f :=
 (NNV_GeometryInstallSlots.any (base m env err r) pred it f).trans
  (NNV_GeometryInstallSlots.any cbase pred it f).symm

theorem zero : (ops m env err r).op6 = canonical.op6 :=
 (NNV_GeometryInstallSlots.zero (base m env err r)).trans
  (NNV_GeometryInstallSlots.zero cbase).symm
#print axioms array
#print axioms iterator
#print axioms mapped
#print axioms empty
#print axioms any
#print axioms zero
end AspisR1.NNV_GeometrySelectedStd
end
