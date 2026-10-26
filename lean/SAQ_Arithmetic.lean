import SAQ_WideABI
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_Arithmetic
open Aeneas Aeneas.Std Result SAQ_WideABI

def add (x y : E) : Result E := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.add (toW x) (toW y)
  ok (fromW z)

def mulK (x y : K) : Result K := do
  let z ← AspisR1CurrentWide.field.QM31.mul (toQ x) (toQ y)
  ok (fromQ z)

def install (ops : SAQ_Query.Ops) : SAQ_Query.Ops :=
  {SAQ_Query.install ops with op2 := add,op9 := mulK}

theorem add_exact (x y z : E) (hx : Port4C_QueryArithmetic.CanonE x)
    (hy : Port4C_QueryArithmetic.CanonE y) (run : add x y=ok z) :
    CheckpointBytes5Output.ofE z=CheckpointBytes5Output.ofE x+CheckpointBytes5Output.ofE y ∧
    Port4C_QueryArithmetic.CanonE z := by
  obtain ⟨out,ho,he⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : fromW out=z := Result.ok.inj he
  subst z
  have result :=  AspisR1CurrentWide.Proof.wide_add_success (toW x) (toW y) out
    ((w_canonical x).mp hx) ((w_canonical y).mp hy) ho
  constructor
  · simpa only [w_decode,toW,fromW,toQ,fromQ] using result.2
  · exact (w_canonical (fromW out)).mpr result.1

theorem mulK_exact (x y z : K) (hx : Port3_FlushInstall.Canonical x)
    (hy : Port3_FlushInstall.Canonical y) (run : mulK x y=ok z) :
    CheckpointBytes5Output.ofK z=CheckpointBytes5Output.ofK x*CheckpointBytes5Output.ofK y ∧
    Port3_FlushInstall.Canonical z := by
  obtain ⟨out,ho,he⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : fromQ out=z := Result.ok.inj he
  subst z
  have result :=  AspisR1CurrentWide.Proof.qm_mul_success (toQ x) (toQ y) out
    ((q_canonical x).mp hx) ((q_canonical y).mp hy) ho
  constructor
  · simpa only [q_decode,toQ,fromQ] using result.2
  · exact (q_canonical (fromQ out)).mpr result.1

structure Remaining (ops : SAQ_Query.Ops) : Prop where
  mulE : ∀ value power product,
    Port4C_QueryArithmetic.CanonE value → Port3_FlushInstall.Canonical power →
    ops.op3 value power=ok product →
    CheckpointBytes5Output.ofE product=CheckpointBytes5Output.ofE value *
      LiteralOpeningView.eK (CheckpointBytes5Output.ofK power) ∧ Port4C_QueryArithmetic.CanonE product
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

#print axioms add_exact
#print axioms mulK_exact
end AspisR1.SAQ_Arithmetic
end
