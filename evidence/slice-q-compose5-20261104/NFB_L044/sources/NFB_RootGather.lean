import NFB_ActualStep
import NFB_GatherFrame
set_option autoImplicit false
noncomputable section
namespace NFB_RootGather
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary NFB_GatherTrace
open NFB_PhysicalFrame NFB_PrivateFrame
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

/-- Physical gather association. The SAME ordered heap writes and terminal
buffers are derived from the actual root, for every raw query array. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize)
 (order : start.val≤finish.val) (bound : finish.val≤22) (heap : Heap)
 (emptyFlat : heap Place.flat.id=some []) (emptyLines : heap Place.lines.id=some []) :
 ∃ (slice : Slice U32) (rows : List Row) (terminal : It) (lines flat : Vec),
  slice.val=(queries.val.drop start.val).take (finish.val-start.val) ∧
  terminal.slice=slice ∧ terminal.i=rows.length ∧
  flat.val=rows.flatMap (fun r=>r.words) ∧ lines.val=rows.map (fun r=>r.lineZ) ∧
  NFB_PhysicalFrame.run (NFB_GatherFrame.actions rows) heap Place.flat.id=some flat.val ∧
  NFB_PhysicalFrame.run (NFB_GatherFrame.actions rows) heap Place.lines.id=some lines.val ∧
  (∀ count, NFB_PhysicalFrame.run ((NFB_GatherFrame.actions rows).take count) heap 0=heap 0) ∧
  Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted
   start terminal lines flat=NFB_GatherChain.stopped
    (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)) := by
 obtain ⟨slice,read,window,length,trace⟩ := NFB_RangeTrace.complete queries start finish order bound
 obtain ⟨rows,terminal,lines,flat,frames,same,cursor,terminalRun⟩ := NFB_GatherChain.chain start trace
 obtain ⟨flatMeaning,lineMeaning⟩ := NET_GeometryGather.meaning frames
 have hf : flat.val=rows.flatMap (fun r=>r.words) := by
  simpa only [alloc.vec.Vec.new,List.nil_append,List.flatMap_map,Function.comp_def] using flatMeaning
 have hl : lines.val=rows.map (fun r=>r.lineZ) := by
  simpa only [alloc.vec.Vec.new,List.nil_append,List.map_map,Function.comp_def] using lineMeaning
 obtain ⟨physicalFlat,physicalLines⟩ := NFB_GatherFrame.payloads rows heap [] [] emptyFlat emptyLines
 refine ⟨slice,rows,terminal,lines,flat,window,same,?_,hf,hl,?_,?_,?_,terminalRun⟩
 · simpa only [Nat.zero_add] using cursor
 · simpa only [List.nil_append,←hf] using physicalFlat
 · simpa only [List.nil_append,←hl] using physicalLines
 · exact fun count=>NFB_GatherFrame.query_frame rows heap count
#print axioms complete
end NFB_RootGather
end
