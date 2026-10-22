import Aeneas
import AspisR1S9CandidateHelperV1.Funs
import AspisR1S9HelperP6.Funs
import S3S9ConcreteFieldOpsV1
open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9CandidateHelperBridgeV1

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

/-- Mapping an operation result through a carrier round trip preserves every
Result constructor. The selected primitive result is kept abstract. -/
theorem mapResult_bind_roundtrip {A B : Type} (f : A → B) (g : B → A)
    (hfg : ∀ x, f (g x) = x) (r : Result B) :
    mapResult f (do let x ← r; ok (g x)) = r := by
  cases r with
  | ok x => simp [mapResult, hfg]
  | fail e => rfl
  | div => rfl

theorem map_qm_mul (x y : AspisR1S9CandidateHelperV1.field.QM31) :
    mapResult AspisR1S9CandidateHelperV1.toP6Q (AspisR1S9CandidateHelperV1.field.QM31.mul x y) =
      @AspisR1S9HelperP6.FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6Q x) (AspisR1S9CandidateHelperV1.toP6Q y) := by
  change mapResult AspisR1S9CandidateHelperV1.toP6Q
    (do let z ← (@AspisR1S9HelperP6.FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6Q x) (AspisR1S9CandidateHelperV1.toP6Q y)); ok (AspisR1S9CandidateHelperV1.fromP6Q z)) = _
  exact mapResult_bind_roundtrip _ _ AspisR1S9CandidateHelperV1.toP6Q_fromP6Q _

theorem map_qm_square (x : AspisR1S9CandidateHelperV1.field.QM31) :
    mapResult AspisR1S9CandidateHelperV1.toP6Q (AspisR1S9CandidateHelperV1.field.QM31.square x) =
      @AspisR1S9HelperP6.FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6Q x) := by
  change mapResult AspisR1S9CandidateHelperV1.toP6Q
    (do let z ← (@AspisR1S9HelperP6.FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6Q x)); ok (AspisR1S9CandidateHelperV1.fromP6Q z)) = _
  exact mapResult_bind_roundtrip _ _ AspisR1S9CandidateHelperV1.toP6Q_fromP6Q _

theorem map_wide_add (x y : AspisR1S9CandidateHelperV1.field.WideExact) :
    mapResult AspisR1S9CandidateHelperV1.toP6W (AspisR1S9CandidateHelperV1.field.WideExact.add x y) =
      @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6W x) (AspisR1S9CandidateHelperV1.toP6W y) := by
  change mapResult AspisR1S9CandidateHelperV1.toP6W
    (do let z ← (@AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6W x) (AspisR1S9CandidateHelperV1.toP6W y)); ok (AspisR1S9CandidateHelperV1.fromP6W z)) = _
  exact mapResult_bind_roundtrip _ _ AspisR1S9CandidateHelperV1.toP6W_fromP6W _

theorem map_wide_mul (x y : AspisR1S9CandidateHelperV1.field.WideExact) :
    mapResult AspisR1S9CandidateHelperV1.toP6W (AspisR1S9CandidateHelperV1.field.WideExact.mul x y) =
      @AspisR1S9HelperP6.FieldOps.wideMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6W x) (AspisR1S9CandidateHelperV1.toP6W y) := by
  change mapResult AspisR1S9CandidateHelperV1.toP6W
    (do let z ← (@AspisR1S9HelperP6.FieldOps.wideMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6W x) (AspisR1S9CandidateHelperV1.toP6W y)); ok (AspisR1S9CandidateHelperV1.fromP6W z)) = _
  exact mapResult_bind_roundtrip _ _ AspisR1S9CandidateHelperV1.toP6W_fromP6W _

theorem map_wide_mul_m31 (x : AspisR1S9CandidateHelperV1.field.WideExact) (y : AspisR1S9CandidateHelperV1.field.M31) :
    mapResult AspisR1S9CandidateHelperV1.toP6W (AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 x y) =
      @AspisR1S9HelperP6.FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6W x) (AspisR1S9CandidateHelperV1.toP6M y) := by
  change mapResult AspisR1S9CandidateHelperV1.toP6W
    (do let z ← (@AspisR1S9HelperP6.FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6W x) (AspisR1S9CandidateHelperV1.toP6M y)); ok (AspisR1S9CandidateHelperV1.fromP6W z)) = _
  exact mapResult_bind_roundtrip _ _ AspisR1S9CandidateHelperV1.toP6W_fromP6W _

theorem map_wide_mul_qm31 (x : AspisR1S9CandidateHelperV1.field.WideExact) (y : AspisR1S9CandidateHelperV1.field.QM31) :
    mapResult AspisR1S9CandidateHelperV1.toP6W (AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 x y) =
      @AspisR1S9HelperP6.FieldOps.wideMulQM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6W x) (AspisR1S9CandidateHelperV1.toP6Q y) := by
  change mapResult AspisR1S9CandidateHelperV1.toP6W
    (do let z ← (@AspisR1S9HelperP6.FieldOps.wideMulQM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (AspisR1S9CandidateHelperV1.toP6W x) (AspisR1S9CandidateHelperV1.toP6Q y)); ok (AspisR1S9CandidateHelperV1.fromP6W z)) = _
  exact mapResult_bind_roundtrip _ _ AspisR1S9CandidateHelperV1.toP6W_fromP6W _

#print axioms mapResult_bind_roundtrip
#print axioms map_qm_mul
#print axioms map_qm_square
#print axioms map_wide_add
#print axioms map_wide_mul
#print axioms map_wide_mul_m31
#print axioms map_wide_mul_qm31

end AspisR1S9CandidateHelperBridgeV1
