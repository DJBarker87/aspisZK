import Port5Q1_QueryPorts
import R17CurrentM31Semantics
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Query
open Aeneas Aeneas.Std Result
abbrev Ops := Port3_NativeQueryBody.Ops

/-- Select the extracted scalar bodies used by the shipped query arithmetic.
All wide, parser, geometry and observation slots are preserved. -/
def install (ops : Ops) : Ops :=
  {ops with
    op4 := ok 0#u32
    op5 := ok 1#u32
    op6 := AspisR1Qm31ArithmeticProbe.field.M31.sub
    op7 := AspisR1Qm31ArithmeticProbe.field.M31.mul
    op8 := S7Kani3BasisOuter.double}

theorem basis (ops : Ops) : Port4C_BasisOuter.SessionABasis (install ops) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem m31 (ops : Ops) : Port5Q1_NodeModel.SessionAM31 (install ops) := by
  constructor
  · intro x y z run
    exact R17CurrentM31Semantics.current_mul_decode x y z run
  · intro x y run
    have h := R17CurrentM31Semantics.current_add_decode x x y run
    change S7JoinBasisMachine.decode y = 2*S7JoinBasisMachine.decode x
    change S7JoinBasisMachine.decode y = S7JoinBasisMachine.decode x + S7JoinBasisMachine.decode x at h
    rw [h]; ring
  · intro x run
    have same : 1#u32=x := Result.ok.inj run
    subst x
    rfl
  · intro x y z run
    exact R17CurrentM31Semantics.current_sub_decode x y z run

/-- Only the primitive rows not discharged by scalar source selection. -/
structure Remaining (ops : Ops) : Prop where
  arithmetic : Port4C_QueryArithmetic.SessionABackends ops
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

theorem primitives (ops : Ops) (rest : Remaining (install ops)) :
    Port5Q1_QueryPorts.SessionAPrimitives (install ops) :=
  ⟨basis ops,rest.arithmetic,m31 ops,rest.decoder,rest.line,rest.line_canonical⟩

/-- Selection does not change any dictionary already bound to these bodies. -/
theorem fixed (ops : Ops) (h : Port4C_BasisOuter.SessionABasis ops) :
    install ops=ops := by
  cases ops
  cases h
  simp_all only [install,Port4C_BasisOuter.SessionABasis.mk.injEq]

#print axioms basis
#print axioms m31
#print axioms primitives
#print axioms fixed
end AspisR1.SAQ_Query
end
