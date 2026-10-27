import RPz7_WAdm_Inventory
import RPz7_TxS_Encoding
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Rc4_Encoding
open Tx1Q_Carriers CheckpointBytes3Namespaces
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem derive {CoreError Hash : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) hash H) :
    TxS_Encoding.Facts run H := by
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run installed reserved query geo D hash
    semantic pub proof split saved run owner ports
  have control := Tx1Q_Control.fields installed reserved query geo D hash semantic pub proof split saved run
  exact ⟨_,TxS_Writer.saved _ hash H oracle (prepared run.p)
    (accumulator {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})
    proof pub saved size fields.queries canonical control.2.2.1 run.writer_call⟩

#print axioms derive
end AspisR1.Rc4_Encoding
end
