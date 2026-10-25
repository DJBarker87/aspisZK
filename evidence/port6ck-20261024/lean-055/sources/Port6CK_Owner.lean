import Port6CK_Checkpoint
import Port6CK_Binding
import Port5Q1_GeometryReads
import Port5Q1_InstallPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Owner
open Aeneas Aeneas.Std Result VTop_Stages
open Port5Q1_QueryPorts
open AspisV8R19.DuplexFrames
variable {CoreError : Type}

/-- One preparation owner interface, scoped to this SAME source input.
The semantic field contains only immutable preparation bindings. -/
structure SessionAPrepare (base : Ops) {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
    (q : Fin 22 → Fin 262144) (rho : OraclePortCheckpointAbiC5.K) : Prop where
  canonical : Port5Q2_Prepared.SessionAPrepare base
  model : ∀ zero g p, base.op1=ok zero →
    base.op7 D semantic proof hash none (Array.repeat 29#usize zero)=ok (.Ok p,g) →
    Port5Q1_QueryPorts.SessionAPrepare p data q rho

/-- One primitive owner interface, retaining exactly the Q1 query, geometry
and domain leaves. No checkpoint, loop, read or output equation is a field. -/
structure SessionAPrimitives (query : Port3_NativeQueryBody.Ops)
    (geometry : Port3_NativeGeometryBody.Ops CoreError) : Prop where
  query : Port5Q1_QueryPorts.SessionAPrimitives query
  geometry : Port5Q1_GeometryCanonical.SessionAPrimitives geometry
  domain : Port5Q1_Domain.SessionADomain geometry
  multiply : geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul
  one : geometry.op7=ok (1#u32)
  inverse : geometry.op11=Port4C_InverseExecution.inverse_owned

theorem release_ports (query : Port3_NativeQueryBody.Ops)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query) :
    Port5Q1_QueryPorts.SessionAPrimitives (Port3_QueryStage.release query) :=
  ⟨ports.basis,ports.arithmetic,ports.m31,ports.decoder,ports.line,ports.line_canonical⟩

theorem release_install (query : Port3_NativeQueryBody.Ops) :
    Port3_QueryStage.release (Port5Q1_QueryPorts.install query)=
      Port5Q1_QueryPorts.install (Port3_QueryStage.release query) := rfl

theorem geometry_install (geometry : Port3_NativeGeometryBody.Ops CoreError) :
    Port4C_GeometryInverse.install (Port4C_CollectStd.install geometry)=
      Port5Q1_GeometryTerminal.install geometry := rfl

#print axioms release_ports
#print axioms release_install
#print axioms geometry_install
end AspisR1.Port6CK_Owner
end
