import RPz7_Tx1Q_Install
import Port5Q1_Ten
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_QueryBridge
open Tx1Q_Carriers

def leaves (ops : Port3_NativeQueryBody.Ops) : Port3_NativeQueryBody.Ops :=
  Port4C_RowStd.install (Port5Q1_QueryPorts.install (Port3_QueryStage.release ops))

theorem release_leaves (ops : Port3_NativeQueryBody.Ops) :
    Port3_QueryStage.release (leaves ops) = leaves ops := rfl

theorem release_ports (ops : Port3_NativeQueryBody.Ops)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives ops) :
    Port5Q1_QueryPorts.SessionAPrimitives (Port3_QueryStage.release ops) :=
  ⟨⟨ports.basis.s3_s4_mul,ports.basis.s3_s4_sub,ports.basis.s3_s4_double,ports.basis.zero,ports.basis.one⟩,
   ⟨ports.arithmetic.s3_s4_s5_mulE,ports.arithmetic.s3_s4_s5_addE,ports.arithmetic.s3_s4_s9_mulK⟩,
   ⟨ports.m31.multiply,ports.m31.double,ports.m31.one,ports.m31.subtract⟩,
   ⟨ports.decoder.decode⟩,ports.line,ports.line_canonical⟩

/-- Concrete Q1 installation compatibility, retaining failures and errors. -/
theorem query_body (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
    (p : C.P) (a : C.A) (g : Array C.E 29#usize)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (geo : C.G) (b : C.B) (stop : Usize) :
    Tx1Q_Install.query (leaves ops) proof p a g obs geo b stop =
      Tx1Q_Install.result (fun x : S.A × S.B => (unAccumulator x.1,unPending x.2))
      (Port3_NativeQueryBody.verifier.candidate.query_loop
        (Port4C_RowStd.install (Port5Q1_QueryPorts.install (Port3_QueryStage.release ops)))
        proof (prepared p) (accumulator a) (arr e g) (observer obs) (geometry geo) (pending b) stop) := by
  unfold Tx1Q_Install.query
  rw [release_leaves]
  rfl

#print axioms release_leaves
#print axioms release_ports
#print axioms query_body
end AspisR1.Tx1Q_QueryBridge
end
