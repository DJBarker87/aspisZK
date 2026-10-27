import RPz7_WAdm_NativeInstance
import RPz7_WAdm_OriginalEndpoint
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_NativeInstall
open Tx1Q_Carriers

def writer {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (p : C.P) (a : C.A) (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) :=
  WAdm_NativeInstance.writer (Tx1Q_Install.digest D) (prepared p) (accumulator a) proof pub hash

/-- Only CurrentCaller writer16 changes. The concrete body is the emitted
fissioned source whose bounded native equivalence is checked by Kani. -/
def install (ops : AspisR1CurrentCaller.Ops) : AspisR1CurrentCaller.Ops := {ops with op16 := writer}

theorem writer_slot (ops : AspisR1CurrentCaller.Ops) : @(install ops).op16 = @writer := rfl

theorem other_slots (ops : AspisR1CurrentCaller.Ops) : {install ops with op16 := ops.op16} = ops := by
  cases ops
  rfl

/-- Accepted-run substitution on the exact same arguments and saved Vec,
with no new successful call or output-agreement premise. -/
theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    (install installed).op16 D run.p {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}
      proof pub hash = ok saved := by
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run installed reserved query geo D hash
    semantic pub proof split saved run owner ports
  have control := Tx1Q_Control.fields installed reserved query geo D hash semantic pub proof split saved run
  exact WAdm_NativeInstance.accepted (Tx1Q_Install.digest D) (prepared run.p)
    (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) proof pub hash saved
    fields size canonical control.2.2.1 run.writer_call

#print axioms writer_slot
#print axioms other_slots
#print axioms on_run
end AspisR1.WAdm_NativeInstall
end
