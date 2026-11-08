import NNH_Run5bGeometrySlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bGeometryReverse
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeGeometryBody

theorem step {C C' : Type} (g : Ops C) (h : Ops C')
 (mul : ∀ x y, g.op9 x y = h.op9 x y)
 (flat pref : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (out : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0_loop0.body g flat pref iter suffix out =
 verifier.QueryGeometry.for_range_loop0_loop0.body h flat pref iter suffix out := by
 simp only [verifier.QueryGeometry.for_range_loop0_loop0.body,mul]

theorem loop {C C' : Type} (g : Ops C) (h : Ops C')
 (mul : ∀ x y, g.op9 x y = h.op9 x y)
 (flat pref : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (out : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0_loop0 g iter flat pref suffix out =
 verifier.QueryGeometry.for_range_loop0_loop0 h iter flat pref suffix out := by
 unfold verifier.QueryGeometry.for_range_loop0_loop0
 apply congrArg (fun f => Aeneas.Std.loop f (iter,suffix,out))
 funext state
 exact step g h mul flat pref state.1 state.2.1 state.2.2

theorem selected (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (flat pref : alloc.vec.Vec U32)
 (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
 (suffix : U32) (out : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0_loop0 (NNH_Run5bGeometrySlots.ops m env err r)
  iter flat pref suffix out =
 verifier.QueryGeometry.for_range_loop0_loop0 NNH_Run5bGeometrySlots.canonical
  iter flat pref suffix out :=
 loop _ _ (NNH_Run5bGeometrySlots.multiply m env err r) flat pref iter suffix out
#print axioms step
#print axioms loop
#print axioms selected
end AspisR1.NNH_Run5bGeometryReverse
end
