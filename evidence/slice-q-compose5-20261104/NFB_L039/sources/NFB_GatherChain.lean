import NFB_GatherTrace
set_option autoImplicit false
noncomputable section
namespace NFB_GatherChain
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFB_GatherTrace NEW_GeometryDictionary

def stopped (result : Result Answer) : Result (ControlFlow (It × Vec × Vec) Answer) :=
 match result with
 | .ok value => .ok (.done value)
 | .fail e => .fail e
 | .div => .div

/-- Every complete partial computation gives ONE ordered append/frame chain
and ONE terminal body on its SAME two final buffers, including error exits.
The terminal body retains the prefix/inverse/reverse/collect calls unchanged. -/
theorem chain (start : Usize) {it : It} {lines flat : Vec} {result : Result Answer}
    (trace : Trace start it lines flat result) :
    ∃ (rows : List Row) (terminal : It) (finalLines finalFlat : Vec),
      NET_GeometryGather.Trace (rows.map (fun r => (r.words,r.lineZ)))
        flat.val lines.val finalFlat.val finalLines.val ∧
      terminal.slice=it.slice ∧ terminal.i=it.i+rows.length ∧
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
        start terminal finalLines finalFlat=stopped result := by
 induction trace with
 | failed it lines flat e observed =>
   exact ⟨[],it,lines,flat,NET_GeometryGather.Trace.done _ _,rfl,by simp,observed⟩
 | diverged it lines flat observed =>
   exact ⟨[],it,lines,flat,NET_GeometryGather.Trace.done _ _,rfl,by simp,observed⟩
 | done it lines flat value observed =>
   exact ⟨[],it,lines,flat,NET_GeometryGather.Trace.done _ _,rfl,by simp,observed⟩
 | step it lines flat it1 lines1 flat1 query row result next observed sameSlice cursor hflat hlines nonzero tail ih =>
   obtain ⟨rows,terminal,finalLines,finalFlat,frames,sliceEq,indexEq,terminalRun⟩ := ih
   refine ⟨row::rows,terminal,finalLines,finalFlat,?_,sliceEq.trans sameSlice,?_,terminalRun⟩
   · exact NET_GeometryGather.Trace.step (row.words,row.lineZ)
       (rows.map (fun r => (r.words,r.lineZ))) flat.val lines.val flat1.val lines1.val
       finalFlat.val finalLines.val hflat hlines
       (by simp only [Port4C_GeometryGather.Row.words,List.length_cons,List.length_nil]) frames
   · simp only [List.length_cons]
     omega

/-- Prefix lengths, exact ordered contents and terminal cursor are all
DERIVED from the SAME full computation, not caller-supplied output choices. -/
theorem complete (start : Usize) (it : It) (lines flat : Vec) (fuel : Nat)
    (remaining : it.i+fuel=it.slice.val.length) :
    ∃ (rows : List Row) (terminal : It) (finalLines finalFlat : Vec),
      finalFlat.val=flat.val++(rows.flatMap (fun r => r.words)) ∧
      finalLines.val=lines.val++(rows.map (fun r => r.lineZ)) ∧
      finalFlat.val.length=flat.val.length+5*rows.length ∧
      finalLines.val.length=lines.val.length+rows.length ∧
      terminal.slice=it.slice ∧ terminal.i=it.i+rows.length ∧
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
        start terminal finalLines finalFlat=stopped (run start it lines flat) := by
 obtain ⟨rows,terminal,finalLines,finalFlat,frames,sliceEq,indexEq,terminalRun⟩ :=
   chain start (NFB_GatherTrace.complete start it lines flat fuel remaining)
 obtain ⟨flatMeaning,lineMeaning⟩ := NET_GeometryGather.meaning frames
 obtain ⟨flatLength,lineLength⟩ := NET_GeometryGather.lengths frames
 refine ⟨rows,terminal,finalLines,finalFlat,?_,?_,?_,?_,sliceEq,indexEq,terminalRun⟩
 · simpa only [List.flatMap_map,Function.comp_def] using flatMeaning
 · simpa only [List.map_map,Function.comp_def] using lineMeaning
 · simpa only [List.length_map] using flatLength
 · simpa only [List.length_map] using lineLength

#print axioms chain
#print axioms complete
end NFB_GatherChain
end
