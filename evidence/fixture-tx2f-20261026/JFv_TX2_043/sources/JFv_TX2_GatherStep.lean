import JFv_TX2_ZeroTest
import JFv_TX2_GeometryOps
import Port4C_GeometryGather
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_GatherStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody

theorem source {C : Type} (ops : Ops C) (start : Usize)
    (it it1 : core.slice.iter.Iter U32) (query : U32) (u parent left right : Usize)
    (row : Port4C_GeometryGather.Row) (zs flat : alloc.vec.Vec U32)
    (next : core.slice.iter.IteratorSliceIter.next it=ok (some query,it1))
    (cast : lift (UScalar.cast .Usize query)=ok u)
    (div : u/4#usize=ok parent)
    (lo : Usize.wrapping_mul parent 4#usize=left)
    (hi : Usize.wrapping_add left 3#usize=right)
    (fu : ops.op12 u=ok (.Ok u)) (fl : ops.op12 left=ok (.Ok left))
    (fr : ops.op12 right=ok (.Ok right))
    (point : ops.op15 u=ok (⟨row.x,row.y⟩ : SAQ_Geometry.Point))
    (lx : ops.op14 left=ok row.lineX) (ly : ops.op14 right=ok row.lineY)
    (node : (do let square ← ops.op9 row.lineX row.lineX
                let doubled ← ops.op10 square
                let one ← ops.op7
                ops.op8 doubled one)=ok row.lineZ)
    (nonzero : ∀ x∈row.words,x≠0#u32)
    (zbound : zs.val.length≤22) (fbound : flat.val.length≤110) :
    ∃ zs1 flat1,
      verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
        start it zs flat=ok (cont (it1,zs1,flat1)) ∧
      zs1.val=zs.val++[row.lineZ] ∧ flat1.val=flat.val++row.words := by
  obtain ⟨square,hs,node⟩ := Port3_PushFrame.bind_success _ _ _ node
  obtain ⟨doubled,hd,node⟩ := Port3_PushFrame.bind_success _ _ _ node
  obtain ⟨one,ho,hz⟩ := Port3_PushFrame.bind_success _ _ _ node
  have zeros := JFv_TX2_ZeroTest.source
    (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
      (Port4C_GeometryStd.install ops)) (⟨row.slice,0⟩ : core.slice.iter.Iter U32) 5
    (by simp [Port4C_GeometryGather.Row.slice,Port4C_GeometryGather.Row.words])
    (by
      intro j hj _
      change verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut
        (Port4C_GeometryStd.install ops) () row.slice.val[j]=ok (false,())
      rw [Port4C_GeometryStd.zero_closure]
      have hn : row.slice.val[j]≠0#u32 := nonzero _ (List.getElem_mem hj)
      simp only [hn,decide_false])
  obtain ⟨zs1,push,pushed⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec zs row.lineZ (by
    have limit : 23≤Usize.max := by scalar_tac
    omega))
  have room : flat.val.length+row.slice.val.length≤Usize.max := by
    have limit : 115≤Usize.max := by scalar_tac
    simp only [Port4C_GeometryGather.Row.slice,Port4C_GeometryGather.Row.words,List.length_cons,List.length_nil]
    omega
  let flat1 : alloc.vec.Vec U32 := ⟨flat.val++row.words,by
    simpa only [List.length_append,Port4C_GeometryGather.Row.slice] using room⟩
  have extend : alloc.vec.Vec.extend_from_slice core.marker.CopyU32.cloneInst flat row.slice=ok flat1 := by
    unfold alloc.vec.Vec.extend_from_slice
    split
    · simp only [Port4C_GeometryStd.clone_m31]
      rfl
    · rename_i bad
      exact False.elim (bad room)
  refine ⟨zs1,flat1,?_,pushed,rfl⟩
  unfold verifier.QueryGeometry.for_range_loop0.body
  rw [next,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [cast,bind_tc_ok]
  simp only [Port4C_GeometryStd.install,fu,Port4C_GeometryStd.mapError,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,Aeneas.Std.uncurry,point,div,lo,hi,lift,fl,lx,fr,ly,hs,hd,ho,hz]
  change (do
    let (bad,_) ← Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter U32)
      (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
        (Port4C_GeometryStd.install ops)) ⟨row.slice,0⟩ ()
    if bad then ok (done (core.result.Result.Err verifier.Error.Query : core.result.Result verifier.QueryGeometry verifier.Error)) else do
      let flat2 ← alloc.vec.Vec.extend_from_slice core.marker.CopyU32.cloneInst flat row.slice
      let zs2 ← alloc.vec.Vec.push zs row.lineZ
      ok (cont (it1,zs2,flat2)))=_
  rw [zeros,bind_tc_ok]
  simp only [Bool.false_eq_true,if_false,extend,push,bind_tc_ok]
#print axioms source
end AspisR1.JFv_TX2_GatherStep
end
