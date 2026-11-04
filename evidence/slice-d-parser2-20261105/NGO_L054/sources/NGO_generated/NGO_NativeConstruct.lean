import NGO_LiftTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_NativeConstruct
open NGD_DecodeTrace AspisR1DecodeKFullV10 NGO_ScheduleState
/-- Original native schedule AND emitted trace are constructed from every
original borrowed fitting window. No Trace/Run is an input hypothesis. -/
theorem construct {N : Usize} {r : Record} {off start : Usize}
    (d : Domain N r off start) (window : Slice U8)
    (same : window.val=((r.framed.val.drop 5).drop (32*off.val)).take (32*N.val)) :
    ∃ (ce : CE) (final : Final N),
      core.slice.Slice.chunks_exact window 32#usize=ok ce ∧
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorChunksExact U8) ce=
          ok {iter:=ce,count:=0#usize} ∧
      Trace d {start:=0#usize,«end»:=N} (Array.repeat N aspis_core.field.QM31.ZERO) final ∧
      NGO_NativeTrace.Run d (state ce 0#usize) (Array.repeat N aspis_core.field.QM31.ZERO) final := by
  have length : window.val.length=32*N.val := by
    rw [same]
    simp only [List.length_take,List.length_drop]
    have fitting:=d.range
    omega
  obtain ⟨ce,chunks,enumerate,values,remainder⟩ := NGO_ChunksNativeStart.construct window N.val length
  have count : ce.chunks.length=N.val := by
    have h:=congrArg List.length values
    simpa only [List.length_map,NGO_ChunkSchedule.window_count] using h
  have originalValues : ce.chunks.map (fun c=>c.val)=
      NGO_ChunkSchedule.windows (((r.framed.val.drop 5).drop (32*off.val)).take (32*N.val)) N.val := by
    simpa only [same] using values
  obtain ⟨final,trace⟩ := NGO_TraceTotal.exists_trace d {start:=0#usize,«end»:=N}
    (Array.repeat N aspis_core.field.QM31.ZERO) rfl (by simp)
  exact ⟨ce,final,chunks,enumerate,trace,NGO_LiftTrace.lift d ce originalValues count _ _ _ trace rfl (by simp)⟩
#print axioms construct
end NGO_NativeConstruct
