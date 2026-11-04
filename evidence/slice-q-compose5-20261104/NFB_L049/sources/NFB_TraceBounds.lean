import NFB_RootGather
set_option autoImplicit false
noncomputable section
namespace NFB_TraceBounds
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryDictionary NFB_GatherTrace

theorem next_active (it it1 : It) (query : U32)
 (next : core.slice.iter.IteratorSliceIter.next it=ok (some query,it1)) :
 it.i < it.slice.val.length := by
 unfold core.slice.iter.IteratorSliceIter.next at next
 split at next
 · assumption
 · cases next

theorem terminal_bound (start : Usize) {it : It} {lines flat : Vec} {result : Result Answer}
 (trace : Trace start it lines flat result) (within : it.i≤it.slice.val.length) :
 ∃ (rows : List Row) (terminal : It) (finalLines finalFlat : Vec),
 NET_GeometryGather.Trace (rows.map (fun r=>(r.words,r.lineZ)))
  flat.val lines.val finalFlat.val finalLines.val ∧
 terminal.slice=it.slice ∧ terminal.i=it.i+rows.length ∧
 terminal.i≤terminal.slice.val.length ∧
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
  start terminal finalLines finalFlat=NFB_GatherChain.stopped result := by
 induction trace with
 | failed it lines flat e observed =>
  exact ⟨[],it,lines,flat,.done _ _,rfl,by simp,within,observed⟩
 | diverged it lines flat observed =>
  exact ⟨[],it,lines,flat,.done _ _,rfl,by simp,within,observed⟩
 | done it lines flat value observed =>
  exact ⟨[],it,lines,flat,.done _ _,rfl,by simp,within,observed⟩
 | step it lines flat it1 lines1 flat1 query row result next observed sameSlice cursor hf hl nz tail ih =>
  have active := next_active it it1 query next
  have within1 : it1.i≤it1.slice.val.length := by rw [sameSlice,cursor];omega
  obtain ⟨rows,terminal,finalLines,finalFlat,frames,same,index,limit,last⟩ := ih within1
  refine ⟨row::rows,terminal,finalLines,finalFlat,?_,same.trans sameSlice,?_,limit,last⟩
  · exact NET_GeometryGather.Trace.step (row.words,row.lineZ) _ _ _ _ _ _ _ hf hl
     (by simp only [Port4C_GeometryGather.Row.words,List.length_cons,List.length_nil]) frames
  · simp only [List.length_cons]
    omega

theorem accepted_end (start : Usize) (it : It) (lines flat : Vec)
 (out : AspisR1Stage2.verifier.QueryGeometry) (within : it.i≤it.slice.val.length)
 (accepted : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
 adopted start it lines flat=ok (done (.Ok out))) : it.i=it.slice.val.length := by
 by_contra h
 have active : it.i < it.slice.val.length := by omega
 have next:=NFB_QueryIterator.next it active
 have impossible:=Port4C_GeometryControl.active_not_done adopted start it
  {it with i:=it.i+1} it.slice.val[it.i] lines flat out next
 rw [NFB_GeometryInstall.standard] at impossible
 exact impossible accepted
#print axioms next_active
#print axioms terminal_bound
#print axioms accepted_end
end NFB_TraceBounds
end
