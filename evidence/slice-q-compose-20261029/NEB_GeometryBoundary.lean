import NEB_ActualGeometryModel
import NEB_PureFrame
set_option autoImplicit false
noncomputable section
namespace NEB_GeometryBoundary
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

theorem invalid_start {S Event CoreError : Type} (state : S) (ops : Ops CoreError)
    (error : CoreError) (queries : Array U32 22#usize) (start stop : Usize)
    (bad : stop.val<start.val) :
    NEB_PureFrame.run (Event:=Event) state
      (Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install
        (NEB_ActualGeometryModel.install ops error)) queries start stop)=
      ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Query,state,[]) := by
  rw [Port3_GeometryStage.invalid_start _ _ _ _ bad]
  rfl

theorem invalid_end {S Event CoreError : Type} (state : S) (ops : Ops CoreError)
    (error : CoreError) (queries : Array U32 22#usize) (start stop : Usize)
    (bad : 22<stop.val) :
    NEB_PureFrame.run (Event:=Event) state
      (Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install
        (NEB_ActualGeometryModel.install ops error)) queries start stop)=
      ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Query,state,[]) := by
  rw [Port3_GeometryStage.invalid_end _ _ _ _ bad]
  rfl

/-- Empty terminal state reaches no prefix, inverse or field port. Its entire
Result is fixed by the actual terminal body, not by a callee-success premise. -/
theorem empty_terminal {CoreError : Type} (ops : Ops CoreError) (error : CoreError)
    (start : Usize) (iter : core.slice.iter.Iter U32) (zs : alloc.vec.Vec U32)
    (ending : iter.slice.val.length≤ iter.i) :
    verifier.QueryGeometry.for_range_loop0.body
      (Port5Q1_GeometryTerminal.install (NEB_ActualGeometryModel.install ops error))
      start iter zs (alloc.vec.Vec.new U32)=
      ok (done (.Ok {start,inverses:=alloc.vec.Vec.new _,line_z:=zs})) := by
  have next : core.slice.iter.IteratorSliceIter.next iter=ok (none,iter) := by
    unfold core.slice.iter.IteratorSliceIter.next
    split
    · rename_i active
      change iter.i< iter.slice.val.length at active
      omega
    · rfl
  have empty : (Port5Q1_GeometryTerminal.install
      (NEB_ActualGeometryModel.install ops error)).op4 Global (alloc.vec.Vec.new U32)=ok true := rfl
  unfold verifier.QueryGeometry.for_range_loop0.body
  rw [next,bind_tc_ok,empty,bind_tc_ok]
  rfl

#print axioms invalid_start
#print axioms invalid_end
#print axioms empty_terminal
end NEB_GeometryBoundary
end
