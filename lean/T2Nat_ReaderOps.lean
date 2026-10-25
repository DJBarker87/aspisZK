import T2Nat_WeightSequence
import T2Nat_SemanticJoin
import Port5Q2_ReaderValidate
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_ReaderOps
open Aeneas Aeneas.Std Result AspisR1Stage2

def unwrap : T2Nat_RawJoin.Unwrap := fun _ =>
  OraclePortCkptAbi2Unwrap.unwrapWithPanic (fun _ => fail .panic)

theorem unwrap_ok (N : Usize) (b : Array U8 N) : unwrap N (.Ok b)=ok b := rfl

/-- Current emitted raw/scalar/semantic/validator/iterator bodies. Allocation,
comparisons and header helpers retain the adopted allocator/Std installation.
The panic implementation is irrelevant on every reached bounded raw read. -/
def ops (reserved : Bool) : ResumeOps :=
  {CheckpointBytes4Ops.ops reserved with
    raw := T2Nat_ScalarJoin.raw unwrap
    readK := T2Nat_ScalarJoin.readK unwrap
    readE := T2Nat_ScalarJoin.readE unwrap
    validate := Port5Q2_ReaderValidate.validate
    readSemanticAlpha := Port5Q2_ReaderSemantic.semantic (T2Nat_ScalarJoin.readK unwrap)
    readWeights := Port5Q2_ReaderWeights.weights (T2Nat_ScalarJoin.readK unwrap)}

theorem raw (reserved : Bool) (N : Usize) (r : verifier.Reader) :
    T2Nat_ResultEq.EqOk ((ops reserved).raw N r) ((CheckpointBytes4Ops.ops reserved).raw N r) :=
  T2Nat_ScalarJoin.raw_eq unwrap unwrap_ok N r

theorem readK (reserved : Bool) (r : verifier.Reader) :
    T2Nat_ResultEq.EqOk ((ops reserved).readK r) ((CheckpointBytes4Ops.ops reserved).readK r) :=
  T2Nat_ScalarJoin.k_eq unwrap unwrap_ok r

theorem readE (reserved : Bool) (r : verifier.Reader) :
    T2Nat_ResultEq.EqOk ((ops reserved).readE r) ((CheckpointBytes4Ops.ops reserved).readE r) :=
  T2Nat_ScalarJoin.e_eq unwrap unwrap_ok r

theorem semantic (reserved : Bool) (bytes : Slice U8) (start : Usize) :
    T2Nat_ResultEq.EqOk ((ops reserved).readSemanticAlpha bytes start)
      ((CheckpointBytes4Ops.ops reserved).readSemanticAlpha bytes start) :=
  T2Nat_SemanticJoin.reference unwrap unwrap_ok bytes start

theorem weights (reserved : Bool) (bytes : Slice U8) (start : Usize)
    (v : alloc.vec.Vec aspis_core.field.QM31) :
    T2Nat_ResultEq.EqOk ((ops reserved).readWeights bytes start v)
      ((CheckpointBytes4Ops.ops reserved).readWeights bytes start v) :=
  T2Nat_WeightSequence.native unwrap unwrap_ok bytes start v

theorem validate (reserved : Bool) (q : Array U32 22#usize) :
    (ops reserved).validate q = (CheckpointBytes4Ops.ops reserved).validate q :=
  Port5Q2_ReaderValidate.reference q

#print axioms unwrap_ok
#print axioms raw
#print axioms readK
#print axioms readE
#print axioms semantic
#print axioms weights
#print axioms validate
end AspisR1.T2Nat_ReaderOps
end
