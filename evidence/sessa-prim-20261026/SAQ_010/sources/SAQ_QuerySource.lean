import SAQ_Arithmetic
import SAQ_MixedSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_QuerySource
open Aeneas Aeneas.Std Result

def install (ops : SAQ_Query.Ops) : SAQ_Query.Ops :=
  {SAQ_Arithmetic.install ops with op3 := SAQ_MixedSource.mulE}

structure Remaining (ops : SAQ_Query.Ops) : Prop where
  decoder : Port5Q1_OpeningValues.SessionAS3 ops
  line : ∀ alpha values inverse value, ops.op16 alpha values inverse=ok value →
    CheckpointBytes5Output.ofE value=FoldRuntimeAlgebra.lineWithInverses
      (CheckpointBytes5Output.ofE alpha)
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 2)))
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 3)))
      (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE
        (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 4)))
      (Port5Q1_OpeningValues.values values)
  line_canonical : ∀ alpha values inverse value,
    ops.op16 alpha values inverse=ok value → Port4C_QueryArithmetic.CanonE value

theorem arithmetic (ops : SAQ_Query.Ops) :
    Port4C_QueryArithmetic.SessionABackends (install ops) :=
  ⟨SAQ_MixedSource.mulE_exact,SAQ_Arithmetic.add_exact,SAQ_Arithmetic.mulK_exact⟩

theorem primitives (ops : SAQ_Query.Ops) (rest : Remaining (install ops)) :
    Port5Q1_QueryPorts.SessionAPrimitives (install ops) :=
  ⟨SAQ_Query.basis ops,arithmetic ops,SAQ_Query.m31 ops,
    rest.decoder,rest.line,rest.line_canonical⟩

#print axioms arithmetic
#print axioms primitives
end AspisR1.SAQ_QuerySource
end
