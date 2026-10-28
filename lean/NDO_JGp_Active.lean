import JFv_TX2_GatherStep
import NDO_JGp_Shape
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Active
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody

theorem source {C : Type} (err : C) (seed : Ops C)
    (it : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
    (slice : it.slice=JGp_Shape.selected)
    (active : it.i<10) (hzs : zs.val=JGp_Shape.zs it.i)
    (hflat : flat.val=JGp_Shape.flat it.i) :
    ∃ zs1 flat1,
      verifier.QueryGeometry.for_range_loop0.body (JFv_TX2_GeometryOps.install err seed)
        0#usize it zs flat=ok (cont ({it with i:=it.i+1},zs1,flat1)) ∧
      zs1.val=JGp_Shape.zs (it.i+1) ∧
      flat1.val=JGp_Shape.flat (it.i+1) := by
  let i : Fin 10 := ⟨it.i,active⟩
  have length : it.slice.val.length=10 := by rw [slice];simp [JGp_Shape.selected]
  have next : core.slice.iter.IteratorSliceIter.next it=
      ok (some (JGp_Rows.query i),{it with i:=it.i+1}) := by
    have read : it.slice.val[it.i]'(by omega)=JGp_Rows.query i := by
      simpa only [slice] using JGp_Shape.query it.i active
    unfold core.slice.iter.IteratorSliceIter.next
    split
    · change ok (some (it.slice.val[it.i]'(by omega)),{it with i:=it.i+1})=_
      rw [read]
    · rename_i bad
      exact False.elim (bad (by change it.i < it.slice.val.length;omega))
  obtain ⟨cast,div,lo,hi⟩ := JGp_Rows.addresses i
  obtain ⟨point,lx,ly,node⟩ := JGp_Rows.source err seed i
  have node1 : (do
      let square ← (JFv_TX2_GeometryOps.install err seed).op9 (JGp_Rows.value i).lineX (JGp_Rows.value i).lineX
      let doubled ← (JFv_TX2_GeometryOps.install err seed).op10 square
      let one ← (JFv_TX2_GeometryOps.install err seed).op7
      (JFv_TX2_GeometryOps.install err seed).op8 doubled one)=ok (JGp_Rows.value i).lineZ := by
    change (do
      let square ← AspisR1Qm31ArithmeticProbe.field.M31.mul (JGp_Rows.value i).lineX (JGp_Rows.value i).lineX
      let doubled ← AspisR1Qm31ArithmeticProbe.field.M31.double square
      let one ← ok (1#u32)
      AspisR1Qm31ArithmeticProbe.field.M31.sub doubled one)=_
    simpa only [JFv_TX2_NodeCall.sourceCall,bind_tc_ok] using node
  obtain ⟨zs1,flat1,run,zval,fval⟩ := JFv_TX2_GatherStep.source
    (JFv_TX2_GeometryOps.install err seed) 0#usize it {it with i:=it.i+1}
    (JGp_Rows.query i) (JGp_Rows.input i 0) (JGp_Rows.parent i)
    (JGp_Rows.input i 1) (JGp_Rows.input i 2) (JGp_Rows.value i) zs flat
    next cast div lo hi (JGp_Rows.fibres err seed i 0)
    (JGp_Rows.fibres err seed i 1) (JGp_Rows.fibres err seed i 2)
    point lx ly node1 (fun x hx => (JGp_Rows.regular i x hx).2)
    (by rw [hzs,(JGp_Shape.lengths _).1];omega)
    (by rw [hflat,(JGp_Shape.lengths _).2];omega)
  refine ⟨zs1,flat1,run,?_,?_⟩
  · rw [zval,hzs,(JGp_Shape.step it.i).1,JGp_Shape.row_eq it.i active]
  · rw [fval,hflat,(JGp_Shape.step it.i).2,JGp_Shape.row_eq it.i active]
#print axioms source
end AspisR1.JGp_Active
end
