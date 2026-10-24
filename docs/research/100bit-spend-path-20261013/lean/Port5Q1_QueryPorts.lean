import Port5Q1_OpeningValues
import Port5Q1_GeometryAccessor
import Port5Q1_NodeModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_QueryPorts
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open CheckpointBytes5Output (ofK ofE)
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FP := ZMod AspisCircleGroupOrder.P

def install (ops : Ops) : Ops :=
  {ops with op11 := Port4B_Opening.opening, op18 := Port5Q1_GeometryBinding.forQuery}

/-- Session A op7 port on the SAME returned Prepared. No query/geometry or
accumulator result is a preparation field. Its concrete instance is upstream. -/
structure SessionAPrepare (p : verifier.Prepared) (data : MatchingSupport.Data FE)
    (q : Fin 22 → Fin 262144) (rho : FK) : Prop where
  queries : ∀ i (hi : i<22),
    (Port5Q1_GeometryBinding.queryAt p.queries i).val=(q ⟨i,hi⟩).val
  rho_eq : ofK p.rho=rho
  rho_canonical : Port3_FlushInstall.Canonical p.rho
  alpha1 : ∀ alpha, Array.index_usize p.alpha 1#usize=ok alpha → ofE alpha=data.alpha1

/-- Named S3/S4/S5/S9 local primitive ports. Each field refers to an actual
helper operand/result, never a parsed query, successful parent or advance. -/
structure SessionAPrimitives (ops : Ops) : Prop where
  basis : Port4C_BasisOuter.SessionABasis ops
  arithmetic : Port4C_QueryArithmetic.SessionABackends ops
  m31 : Port5Q1_NodeModel.SessionAM31 ops
  decoder : Port5Q1_OpeningValues.SessionAS3 ops
  line : ∀ alpha values inverse value, ops.op16 alpha values inverse=ok value →
    ofE value=FoldRuntimeAlgebra.lineWithInverses (ofE alpha)
      (algebraMap FP FE (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)))
      (algebraMap FP FE (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)))
      (algebraMap FP FE (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)))
      (Port5Q1_OpeningValues.values values)
  line_canonical : ∀ alpha values inverse value,
    ops.op16 alpha values inverse=ok value → Port4C_QueryArithmetic.CanonE value

#print install
end AspisR1.Port5Q1_QueryPorts
end
