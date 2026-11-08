import NNV_GeometryBranches
import NNV_GeometrySelectedStd
import NNV_GeometryPrefixSelected
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryTerminal
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeGeometryBody
open NNH_Run5bGeometrySlots

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (start : Usize) (zs flat : alloc.vec.Vec U32) :
 NNV_GeometryBranches.terminal (ops m env err r) start zs flat =
 NNV_GeometryBranches.terminal canonical start zs flat := by
 have gather := NNV_GeometryCallbacks.gather_outer (ops m env err r) canonical
  (NNV_GeometrySelectedStd.array m env err r)
 simp only [NNV_GeometryBranches.terminal,NNV_GeometrySelectedStd.empty,
  NNV_GeometryPrefixSelected.source,NNH_Run5bGeometrySlots.inverse,
  NNV_GeometrySelectedStd.zero,NNH_Run5bGeometryReverse.selected,
  NNV_GeometrySelectedStd.iterator,NNV_GeometrySelectedStd.mapped,gather]
#print axioms source
end AspisR1.NNV_GeometryTerminal
end
