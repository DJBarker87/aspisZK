import Tx1Q_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_RunCalls
open Aeneas Aeneas.Std Result Tx1Q_Carriers
 theorem source {C H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (slots : Tx1Q_Execution.Slots installed reserved query geo) :
    installed.op20 .S2=ok (.Ok run.initial) ∧
    installed.op19 run.p.queries 0#usize split=ok (.Ok run.geometry) ∧
    installed.op18 run.initial.weights.deref=ok (.Ok run.pending) ∧
    installed.op7 proof run.p run.initial run.scratch none run.geometry run.pending split=ok (.Ok (run.out,run.after)) ∧
    installed.op17 run.after run.out.weights.deref=ok run.flushed ∧
    installed.op16 D run.p {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩} proof pub hash=ok saved := by
  have equal := run.split_eq
  subst split
  rw [slots.initial,slots.geometry,slots.pending,slots.query,slots.flush,slots.writer]
  refine ⟨?_,?_,?_,?_,?_,run.writer_call⟩
  · simp only [Tx1Q_PrefixInstall.initial,variant,Tx1Q_PrefixInstall.topResult,run.initial_call,
      bind_tc_ok,current_roundtrip]
  · simp only [Tx1Q_PrefixInstall.geometryBody,Tx1Q_PrefixInstall.topResult,run.geometry_call,bind_tc_ok]
    rfl
  · have pending := run.pending_call
    change Port3_NativePendingInstall.source reserved (slice k run.initial.weights.deref)=_ at pending
    simp only [Tx1Q_PrefixInstall.newPending,Tx1Q_PrefixInstall.topResult,pending,bind_tc_ok,current_pending_roundtrip]
  · simp only [Tx1Q_Install.query,Tx1Q_Install.result,Tx1Q_QueryBridge.release_leaves,
      observer,Option.map_none,run.query_call,bind_tc_ok,current_roundtrip,current_pending_roundtrip]
  · have flush := run.flush_call
    change Port3_FlushInstall.flush (pending run.after) (slice k run.out.weights.deref)=_ at flush
    unfold Tx1Q_Install.flush
    rw [flush]
    simp only [bind_tc_ok,slice,List.map_map,Function.comp_def,unK_k,List.map_id_fun']
    rfl
#print axioms source
end AspisR1.F3S_RunCalls
end
