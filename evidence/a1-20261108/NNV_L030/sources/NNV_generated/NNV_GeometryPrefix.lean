import NNH_Run5bGeometrySlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryPrefix
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody
/-- The prefix-products callee depends on exactly mul/one, at an arbitrary slice. -/
theorem source {C D : Type} (g : Ops C) (h : Ops D)
 (mul : g.op9 = h.op9) (one : g.op7 = h.op7) (s : Slice U32) :
 (Port5Q1_GeometryTerminal.install g).op13 s =
 (Port5Q1_GeometryTerminal.install h).op13 s := by
 change Port4C_GeometryInverse.prefixCall g s = Port4C_GeometryInverse.prefixCall h s
 unfold Port4C_GeometryInverse.prefixCall Port4C_GeometryInverse.leaves
 rw [mul,one]

theorem selected (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (s : Slice U32) :
 (NNH_Run5bGeometrySlots.ops m env err r).op13 s = NNH_Run5bGeometrySlots.canonical.op13 s :=
 source _ _ (funext (NNH_Run5bGeometrySlots.multiply m env err r))
  (NNH_Run5bGeometrySlots.one m env err r) s
#print axioms source
#print axioms selected
end AspisR1.NNV_GeometryPrefix
end
