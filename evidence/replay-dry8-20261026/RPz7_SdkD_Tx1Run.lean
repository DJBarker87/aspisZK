import RPz7_SdkD_Tx1Suffix
import RPz7_Tx1Q_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_Tx1Run
open Aeneas Aeneas.Std Result AspisR1CurrentCaller Tx1Q_Execution Tx1Q_Carriers
attribute [local irreducible] verifier.candidate.tx1 verifier.candidate.prepare
  Port3_Initial.constructor Port3_NativePendingInstall.source
  Port3_GeometryStage.geometry Port3_FlushInstall.flush Port3_CheckpointInstall.writer
theorem accepted {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (slots : Slots installed reserved query geo)
    (start : compact.OFF_FOLDED_ROOT installed = ok 7751#usize)
    (finish : compact.OFF_ROUND1 installed = ok 7783#usize)
    (success : AspisR1CurrentCaller.verifier.candidate.tx1 installed
      D semantic pub proof split hash none = ok (.Ok saved)) :
    ∃ run : Run installed reserved query geo D hash semantic pub proof split saved,
      aspis_core.field.wide_exact.WideExact.ZERO installed = ok run.zero ∧
      ∃ view : Slice U8,
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          proof {start:=7751#usize,«end»:=7783#usize} = ok view ∧
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok run.root) := by
  obtain ⟨hs,variant,zero,p,scratch,hshape,hscan,hzero,hprep,htail⟩ :=
    AspisR1CurrentCaller.Tx1Reachability.tx1_success _ D semantic pub proof split hash saved success
  have splitEq : split = 10#usize := by
    simpa only [AspisR1CurrentCaller.compact.SPLIT] using hs
  cases splitEq
  obtain ⟨a,root,geometry,b,out,after,flushed,view,hrange,hcopy,hinit,hbatch,hgeo,hpending,hquery,hflush,hwriter⟩ :=
    SdkD_Tx1Suffix.suffix _ D pub proof 10#usize hash p scratch saved start finish htail
  rw [slots.initial] at hinit
  rw [slots.pending] at hpending
  rw [slots.geometry] at hgeo
  rw [slots.query] at hquery
  rw [slots.flush] at hflush
  rw [slots.writer] at hwriter
  have init := Tx1Q_PrefixInstall.initial_success reserved a hinit
  have pend := Tx1Q_PrefixInstall.pending_success reserved a.weights.deref b hpending
  have geom := Tx1Q_PrefixInstall.geometry_success geo p.queries 0#usize 10#usize geometry hgeo
  have qry := Tx1Q_Install.query_success (Tx1Q_QueryBridge.leaves query) proof p a out scratch none
    geometry b after 10#usize hquery
  rw [Tx1Q_QueryBridge.release_leaves] at qry
  have fl := Tx1Q_Install.flush_success after out.weights.deref flushed hflush
  exact ⟨⟨p,zero,scratch,a,root,geometry,b,out,after,flushed,rfl,hprep,init,hbatch,geom,pend,qry,fl,hwriter⟩,hzero,view,hrange,hcopy⟩

#print axioms accepted
end AspisR1.SdkD_Tx1Run
end
