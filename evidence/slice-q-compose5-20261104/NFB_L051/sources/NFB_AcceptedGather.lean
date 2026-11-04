import NFB_TraceBounds
set_option autoImplicit false
noncomputable section
namespace NFB_AcceptedGather
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary NFB_GatherTrace
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem complete (queries : Array U32 22#usize) (start finish : Usize)
 (order : start.val≤finish.val) (bound : finish.val≤22)
 (out : AspisR1Stage2.verifier.QueryGeometry)
 (accepted : resultMap answer
  (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)=ok (.Ok out)) :
 ∃ (rows : List Row) (terminal : It) (lines flat : Vec),
 rows.length=finish.val-start.val ∧
 flat.val=rows.flatMap (fun r=>r.words) ∧ lines.val=rows.map (fun r=>r.lineZ) ∧
 flat.val.length=5*(finish.val-start.val) ∧ lines.val.length=finish.val-start.val ∧
 terminal.i=terminal.slice.val.length ∧
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
  start terminal lines flat=ok (done (.Ok out)) := by
 obtain ⟨slice,read,window,length,trace⟩ := NFB_RangeTrace.complete queries start finish order bound
 rw [accepted] at trace
 obtain ⟨rows,terminal,lines,flat,frames,same,cursor,within,last⟩ :=
  NFB_TraceBounds.terminal_bound start trace (by omega)
 have ending := NFB_TraceBounds.accepted_end start terminal lines flat out within last
 have count : rows.length=finish.val-start.val := by
  simp only [Nat.zero_add] at cursor
  rw [same] at ending
  omega
 obtain ⟨flatMeaning,lineMeaning⟩ := NET_GeometryGather.meaning frames
 obtain ⟨flatLength,lineLength⟩ := NET_GeometryGather.lengths frames
 refine ⟨rows,terminal,lines,flat,count,?_,?_,?_,?_,ending,last⟩
 · simpa only [alloc.vec.Vec.new,List.nil_append,List.flatMap_map,Function.comp_def] using flatMeaning
 · simpa only [alloc.vec.Vec.new,List.nil_append,List.map_map,Function.comp_def] using lineMeaning
 · simpa only [alloc.vec.Vec.new,List.length_nil,List.length_map,Nat.zero_add,count] using flatLength
 · simpa only [alloc.vec.Vec.new,List.length_nil,List.length_map,Nat.zero_add,count] using lineLength
#print axioms complete
end NFB_AcceptedGather
end
