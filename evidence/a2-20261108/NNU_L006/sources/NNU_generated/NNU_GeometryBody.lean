import NNU_GeometryInstall
import NNU_GeometryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_GeometryBody
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody

theorem step {C C' : Type} (g : Ops C) (h : Ops C')
 (mapg : @g.op2 = @Port4C_GeometryStd.mapError)
 (maph : @h.op2 = @Port4C_GeometryStd.mapError)
 (map1 : @g.op1 = @h.op1) (any3 : @g.op3 = @h.op3) (empty4 : @g.op4 = @h.op4)
 (zero6 : g.op6 = h.op6) (one7 : g.op7 = h.op7)
 (sub8 : g.op8 = h.op8) (mul9 : g.op9 = h.op9) (double10 : g.op10 = h.op10)
 (inv11 : g.op11 = h.op11) (pref13 : g.op13 = h.op13)
 (line14 : g.op14 = h.op14) (point15 : g.op15 = h.op15)
 (maps : @g.mapIterator = @h.mapIterator)
 (gather : verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 g =
   verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 h)
 (zero : verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool g =
   verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool h)
 (index : ∀ u, NNH_Run5bIndexLaw.erase (g.op12 u) = NNH_Run5bIndexLaw.erase (h.op12 u))
 (start : Usize) (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0.body g start iter zs flat =
 verifier.QueryGeometry.for_range_loop0.body h start iter zs flat := by
 unfold verifier.QueryGeometry.for_range_loop0.body
 apply bind_congr
 intro pair
 rcases pair with ⟨next,iter1⟩
 cases next with
 | none =>
  simp only [empty4,pref13,inv11,zero6,map1,maps,gather,
   NNH_Run5bGeometryReverse.loop g h (fun x y=>congrFun (congrFun mul9 x) y)]
 | some query =>
  apply bind_congr
  intro u
  simp only [mapg,maph]
  rw [NNU_GeometryIndex.after_map g u _ (fun _=>rfl),
      NNU_GeometryIndex.after_map h u _ (fun _=>rfl),index]
  apply bind_congr
  intro reply
  cases reply with
  | Err e => rfl
  | Ok val =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
   rw [point15]
   apply bind_congr
   intro point
   apply bind_congr
   intro i
   apply bind_congr
   intro i1
   rw [NNU_GeometryIndex.after_map g i1 _ (fun _=>rfl),
       NNU_GeometryIndex.after_map h i1 _ (fun _=>rfl),index]
   apply bind_congr
   intro reply
   cases reply with
   | Err e => rfl
   | Ok val1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    rw [line14]
    apply bind_congr
    intro line_x
    apply bind_congr
    intro i2
    apply bind_congr
    intro i3
    rw [NNU_GeometryIndex.after_map g i3 _ (fun _=>rfl),
        NNU_GeometryIndex.after_map h i3 _ (fun _=>rfl),index]
    simp only [line14,mul9,double10,one7,sub8,any3,zero]
#print axioms step
end AspisR1.NNU_GeometryBody
end
