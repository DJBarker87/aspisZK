import RPz7_WAdm_RunInventory
import RPz7_WAdm_RunDomain
import RPz7_WAdm_Carrier
import RPz7_Tx1Q_Endpoint
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_ReferenceRun
open Tx1Q_Carriers

/-- Change only the proved writer-call observation on this SAME preparation,
query, flush and saved value. No new execution or independent success. -/
def reference {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : WAdm_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved where
  p := run.p
  zero := run.zero
  scratch := run.scratch
  initial := run.initial
  root := run.root
  geometry := run.geometry
  pending := run.pending
  out := run.out
  after := run.after
  flushed := run.flushed
  split_eq := run.split_eq
  prepare_call := run.prepare_call
  initial_call := run.initial_call
  batch_call := run.batch_call
  geometry_call := run.geometry_call
  pending_call := run.pending_call
  query_call := run.query_call
  flush_call := run.flush_call
  writer_call := by
    obtain ⟨fields,size,canonical⟩ := WAdm_RunInventory.on_run installed reserved query geo D hash
      semantic pub proof split saved run owner ports
    have control := WAdm_RunControl.fields installed reserved query geo D hash
      semantic pub proof split saved run
    rw [← WAdm_SourceWriter.writer_eq (Tx1Q_Install.digest D) (prepared run.p)
      (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) proof pub hash
      fields size canonical control.2.2.1]
    exact run.writer_call

theorem same_inputs {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : WAdm_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    let ref := reference installed reserved query geo D hash semantic pub proof split saved run owner ports
    ref.p = run.p ∧ ref.scratch = run.scratch ∧ ref.out = run.out ∧ ref.flushed = run.flushed :=
  ⟨rfl,rfl,rfl,rfl⟩

#print axioms reference
#print axioms same_inputs
end AspisR1.WAdm_ReferenceRun
end
