import NFB_GeometryInstall
import NFB_QueryIterator
import NET_GeometryGather
set_option autoImplicit false
noncomputable section
namespace NFB_GatherTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryDictionary
abbrev It := core.slice.iter.Iter U32
abbrev Vec := alloc.vec.Vec U32
abbrev Answer := core.result.Result AspisR1Stage2.verifier.QueryGeometry AspisR1Stage2.verifier.Error
abbrev Row := Port4C_GeometryGather.Row

def run (start : Usize) (it : It) (lines flat : Vec) : Result Answer :=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 adopted it start lines flat

/-- One SAME-state trace, including failures, divergence and early rejection.
Every continuation retains its actual query and both exact mutable outputs. -/
inductive Trace (start : Usize) : It → Vec → Vec → Result Answer → Prop
 | failed (it : It) (lines flat : Vec) (e : Aeneas.Std.Error)
     (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat=fail e) :
     Trace start it lines flat (fail e)
 | diverged (it : It) (lines flat : Vec)
     (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat=div) :
     Trace start it lines flat div
 | done (it : It) (lines flat : Vec) (value : Answer)
     (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat=ok (ControlFlow.done value)) :
     Trace start it lines flat (ok value)
 | step (it : It) (lines flat : Vec) (it1 : It) (lines1 flat1 : Vec)
     (query : U32) (row : Row) (result : Result Answer)
     (next : core.slice.iter.IteratorSliceIter.next it=ok (some query,it1))
     (observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat=ok (cont (it1,lines1,flat1)))
     (sameSlice : it1.slice=it.slice) (cursor : it1.i=it.i+1)
     (flatFrame : flat1.val=flat.val++row.words)
     (lineFrame : lines1.val=lines.val++[row.lineZ])
     (nonzero : ∀ x∈row.words,x≠0#u32)
     (tail : Trace start it1 lines1 flat1 result) : Trace start it lines flat result

/-- Trace existence is DERIVED from the actual adopted partial computation;
there is no inner success, independently selected output, or trace premise. -/
theorem complete (start : Usize) (it : It) (lines flat : Vec) (fuel : Nat)
    (remaining : it.i+fuel=it.slice.val.length) :
    Trace start it lines flat (run start it lines flat) := by
 induction fuel generalizing it lines flat with
 | zero =>
   have next : core.slice.iter.IteratorSliceIter.next it=ok (none,it) :=
    NFB_QueryIterator.end_next it (by omega)
   unfold run Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0
   rw [loop.eq_def]
   simp only [uncurry]
   cases observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat with
   | fail e => exact Trace.failed it lines flat e observed
   | div => exact Trace.diverged it lines flat observed
   | ok flow =>
    cases flow with
    | done value => exact Trace.done it lines flat value observed
    | cont after =>
     rcases after with ⟨it1,lines1,flat1⟩
     have impossible := Port4C_GeometryControl.terminal_not_cont adopted start it it it1
       lines flat lines1 flat1 next
     rw [NFB_GeometryInstall.standard] at impossible
     exact False.elim (impossible observed)
 | succ fuel ih =>
   have active : it.i < it.slice.val.length := by omega
   let query := it.slice.val[it.i]
   let it1 : It := {it with i:=it.i+1}
   have next : core.slice.iter.IteratorSliceIter.next it=ok (some query,it1) :=
    NFB_QueryIterator.next it active
   unfold run Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0
   rw [loop.eq_def]
   simp only [uncurry]
   cases observed : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start it lines flat with
   | fail e => exact Trace.failed it lines flat e observed
   | div => exact Trace.diverged it lines flat observed
   | ok flow =>
    cases flow with
    | done value => exact Trace.done it lines flat value observed
    | cont after =>
     rcases after with ⟨itOut,lines1,flat1⟩
     have sourceStep : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
         (Port4C_GeometryStd.install adopted) start it lines flat=ok (cont (itOut,lines1,flat1)) := by
      rw [NFB_GeometryInstall.standard]
      exact observed
     obtain ⟨row,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
       Port4C_GeometryGather.step adopted start it it1 itOut query lines lines1 flat flat1 next sourceStep
     rcases fields with ⟨same,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,nonzero,hflat,hlines⟩
     subst itOut
     have tail := ih it1 lines1 flat1 (by dsimp only [it1];omega)
     exact Trace.step it lines flat it1 lines1 flat1 query row _ next observed rfl rfl hflat hlines nonzero tail

#print axioms complete
end NFB_GatherTrace
end
