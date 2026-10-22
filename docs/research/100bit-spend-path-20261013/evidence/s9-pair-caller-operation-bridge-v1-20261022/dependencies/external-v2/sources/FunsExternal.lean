import Aeneas
import AspisR1S9PairCallerStepV1.Types
import AspisR1S9HelperP6.Funs
import S3S9ConcreteFieldOpsV1
import S3ActualFieldOpsComplete
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairCallerStepV1

def toP6M (x : field.M31) : AspisR1S9HelperP6.field.M31 := x
def fromP6M (x : AspisR1S9HelperP6.field.M31) : field.M31 := x

def toP6CM (x : field.CM31) : AspisR1S9HelperP6.field.CM31 :=
  ⟨toP6M x.a, toP6M x.b⟩
def fromP6CM (x : AspisR1S9HelperP6.field.CM31) : field.CM31 :=
  ⟨fromP6M x.a, fromP6M x.b⟩

def toP6Q (x : field.QM31) : AspisR1S9HelperP6.field.QM31 :=
  ⟨toP6CM x.c0, toP6CM x.c1⟩
def fromP6Q (x : AspisR1S9HelperP6.field.QM31) : field.QM31 :=
  ⟨fromP6CM x.c0, fromP6CM x.c1⟩

def toP6W (x : field.WideExact) : AspisR1S9HelperP6.field.WideExact :=
  ⟨toP6Q x.c0, toP6Q x.c1⟩
def fromP6W (x : AspisR1S9HelperP6.field.WideExact) : field.WideExact :=
  ⟨fromP6Q x.c0, fromP6Q x.c1⟩

theorem toP6M_fromP6M (x : AspisR1S9HelperP6.field.M31) :
    toP6M (fromP6M x) = x := rfl
theorem fromP6M_toP6M (x : field.M31) : fromP6M (toP6M x) = x := rfl

theorem toP6Q_fromP6Q (x : AspisR1S9HelperP6.field.QM31) :
    toP6Q (fromP6Q x) = x := by
  cases x with | mk c0 c1 => cases c0 <;> cases c1 <;> rfl
theorem fromP6Q_toP6Q (x : field.QM31) : fromP6Q (toP6Q x) = x := by
  cases x with | mk c0 c1 => cases c0 <;> cases c1 <;> rfl

theorem toP6W_fromP6W (x : AspisR1S9HelperP6.field.WideExact) :
    toP6W (fromP6W x) = x := by
  cases x with
  | mk c0 c1 =>
      change AspisR1S9HelperP6.field.WideExact.mk
        (toP6Q (fromP6Q c0)) (toP6Q (fromP6Q c1)) =
        AspisR1S9HelperP6.field.WideExact.mk c0 c1
      rw [toP6Q_fromP6Q, toP6Q_fromP6Q]
theorem fromP6W_toP6W (x : field.WideExact) :
    fromP6W (toP6W x) = x := by
  cases x with
  | mk c0 c1 =>
      change field.WideExact.mk
        (fromP6Q (toP6Q c0)) (fromP6Q (toP6Q c1)) =
        field.WideExact.mk c0 c1
      rw [fromP6Q_toP6Q, fromP6Q_toP6Q]

def fromActualCM
    (x : AspisR1GroupedPairActualFieldOpsV3.field.CM31) : field.CM31 :=
  ⟨x.a, x.b⟩
def fromActualQ
    (x : AspisR1GroupedPairActualFieldOpsV3.field.QM31) : field.QM31 :=
  ⟨fromActualCM x.c0, fromActualCM x.c1⟩
def fromActualW
    (x : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S) : field.WideExact :=
  ⟨fromActualQ x.c0, fromActualQ x.c1⟩

/-- The six arithmetic leaves use the same selected concrete P6 operations as
the accepted helper adapter. -/
def field.QM31.mul (x y : field.QM31) : Result field.QM31 := do
  let z ← @AspisR1S9HelperP6.FieldOps.qmMul
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toP6Q x) (toP6Q y)
  ok (fromP6Q z)

def field.QM31.square (x : field.QM31) : Result field.QM31 := do
  let z ← @AspisR1S9HelperP6.FieldOps.qmSquare
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toP6Q x)
  ok (fromP6Q z)

def field.WideExact.add (x y : field.WideExact) : Result field.WideExact := do
  let z ← @AspisR1S9HelperP6.FieldOps.wideAdd
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toP6W x) (toP6W y)
  ok (fromP6W z)

def field.WideExact.mul (x y : field.WideExact) : Result field.WideExact := do
  let z ← @AspisR1S9HelperP6.FieldOps.wideMul
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toP6W x) (toP6W y)
  ok (fromP6W z)

def field.WideExact.mul_m31 (x : field.WideExact) (y : field.M31) :
    Result field.WideExact := do
  let z ← @AspisR1S9HelperP6.FieldOps.wideMulM31
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toP6W x) (toP6M y)
  ok (fromP6W z)

def field.WideExact.mul_qm31 (x : field.WideExact) (y : field.QM31) :
    Result field.WideExact := do
  let z ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toP6W x) (toP6Q y)
  ok (fromP6W z)

/-- The pair caller's field reader is backed by the retained actual field
decoder owner, then transferred to this extraction's structurally identical
carrier. Its successful source-parser readback is supplied by the S3 field
readback theorem; this adapter introduces no independent field-value premise. -/
def weights.field (bytes : Slice Std.U8) (i : Std.Usize) :
    Result field.WideExact := do
  let value ← AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decodeField
    bytes i
  ok (fromActualW value)

/-- S2-only extraction adapter: the S1/D fallback is deliberately rejected if
reached. S2 caller theorems must prove `variant = S2` before unfolding the
projection; this is not a model of the other variants. -/
def weights.twofold_libra_weights (_low : Array field.WideExact (16#usize))
    (_extra : Array field.QM31 (2#usize)) :
    Result (Array field.WideExact (4#usize)) := .fail Error.panic

end AspisR1S9PairCallerStepV1
