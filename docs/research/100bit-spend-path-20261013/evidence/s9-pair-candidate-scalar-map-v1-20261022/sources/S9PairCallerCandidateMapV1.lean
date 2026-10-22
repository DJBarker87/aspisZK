import AspisR1S9PairCallerStepV1.Funs
import AspisR1S9CandidateHelperV1.Funs
import S9PairCallerStepOperationBridgeV1
import S9CandidateHelperOperationBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairCallerCandidateMapV1


/-- Result map used only to state carrier transport; fail and div are kept. -/
def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_comp {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
    mapResult g (mapResult f r) = mapResult (g ∘ f) r := by
  cases r <;> rfl

theorem mapResult_injective {A B : Type} (f : A → B)
    (hf : Function.Injective f) : Function.Injective (mapResult f) := by
  intro x y h
  cases x with
  | ok x =>
      cases y with
      | ok y =>
          have hxy : f x = f y := Result.ok.inj h
          exact congrArg Result.ok (hf hxy)
      | fail e => simp [mapResult] at h
      | div => simp [mapResult] at h
  | fail e =>
      cases y with
      | ok y => simp [mapResult] at h
      | fail e' =>
          have he : e = e' := Result.fail.inj h
          subst e'
          rfl
      | div => simp [mapResult] at h
  | div =>
      cases y with
      | ok y => simp [mapResult] at h
      | fail e => simp [mapResult] at h
      | div => rfl

def pairToCandidateM (x : AspisR1S9PairCallerStepV1.field.M31) : AspisR1S9CandidateHelperV1.field.M31 :=
  AspisR1S9CandidateHelperV1.fromP6M (AspisR1S9PairCallerStepV1.toP6M x)
def pairToCandidateCM (x : AspisR1S9PairCallerStepV1.field.CM31) : AspisR1S9CandidateHelperV1.field.CM31 :=
  AspisR1S9CandidateHelperV1.fromP6CM (AspisR1S9PairCallerStepV1.toP6CM x)
def pairToCandidateQ (x : AspisR1S9PairCallerStepV1.field.QM31) : AspisR1S9CandidateHelperV1.field.QM31 :=
  AspisR1S9CandidateHelperV1.fromP6Q (AspisR1S9PairCallerStepV1.toP6Q x)
def pairToCandidateW (x : AspisR1S9PairCallerStepV1.field.WideExact) : AspisR1S9CandidateHelperV1.field.WideExact :=
  AspisR1S9CandidateHelperV1.fromP6W (AspisR1S9PairCallerStepV1.toP6W x)

theorem candidateToP6_pairToCandidateM (x : AspisR1S9PairCallerStepV1.field.M31) :
    AspisR1S9CandidateHelperV1.toP6M (pairToCandidateM x) = AspisR1S9PairCallerStepV1.toP6M x := by
  simp [pairToCandidateM, AspisR1S9CandidateHelperV1.toP6M_fromP6M]
theorem candidateToP6_pairToCandidateQ (x : AspisR1S9PairCallerStepV1.field.QM31) :
    AspisR1S9CandidateHelperV1.toP6Q (pairToCandidateQ x) = AspisR1S9PairCallerStepV1.toP6Q x := by
  simp [pairToCandidateQ, AspisR1S9CandidateHelperV1.toP6Q_fromP6Q]
theorem candidateToP6_pairToCandidateW (x : AspisR1S9PairCallerStepV1.field.WideExact) :
    AspisR1S9CandidateHelperV1.toP6W (pairToCandidateW x) = AspisR1S9PairCallerStepV1.toP6W x := by
  simp [pairToCandidateW, AspisR1S9CandidateHelperV1.toP6W_fromP6W]

theorem candidateToP6_injective_Q : Function.Injective AspisR1S9CandidateHelperV1.toP6Q := by
  intro x y h
  have h' := congrArg AspisR1S9CandidateHelperV1.fromP6Q h
  simpa [AspisR1S9CandidateHelperV1.fromP6Q_toP6Q] using h'
theorem candidateToP6_injective_W : Function.Injective AspisR1S9CandidateHelperV1.toP6W := by
  intro x y h
  have h' := congrArg AspisR1S9CandidateHelperV1.fromP6W h
  simpa [AspisR1S9CandidateHelperV1.fromP6W_toP6W] using h'

/-- The pair caller's concrete operation wrappers and candidate helper's
wrappers map to the same selected P6 slot, with all Result cases preserved. -/
theorem pair_qm_mul_maps_to_candidate (x y : AspisR1S9PairCallerStepV1.field.QM31) :
    mapResult pairToCandidateQ (AspisR1S9PairCallerStepV1.field.QM31.mul x y) =
      AspisR1S9CandidateHelperV1.field.QM31.mul (pairToCandidateQ x) (pairToCandidateQ y) := by
  apply mapResult_injective AspisR1S9CandidateHelperV1.toP6Q candidateToP6_injective_Q
  calc
    mapResult AspisR1S9CandidateHelperV1.toP6Q (mapResult pairToCandidateQ (AspisR1S9PairCallerStepV1.field.QM31.mul x y)) =
        mapResult AspisR1S9PairCallerStepV1.toP6Q (AspisR1S9PairCallerStepV1.field.QM31.mul x y) := by
          cases AspisR1S9PairCallerStepV1.field.QM31.mul x y <;>
            simp [mapResult, pairToCandidateQ, AspisR1S9CandidateHelperV1.toP6Q_fromP6Q]
    _ = @AspisR1S9HelperP6.FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9PairCallerStepV1.toP6Q x) (AspisR1S9PairCallerStepV1.toP6Q y) :=
      AspisR1S9PairCallerStepOperationBridgeV1.map_qm_mul x y
    _ = mapResult AspisR1S9CandidateHelperV1.toP6Q (AspisR1S9CandidateHelperV1.field.QM31.mul (pairToCandidateQ x)
          (pairToCandidateQ y)) := by
          symm
          change AspisR1S9CandidateHelperBridgeV1.mapResult AspisR1S9CandidateHelperV1.toP6Q
            (AspisR1S9CandidateHelperV1.field.QM31.mul (pairToCandidateQ x) (pairToCandidateQ y)) = _
          exact AspisR1S9CandidateHelperBridgeV1.map_qm_mul (pairToCandidateQ x) (pairToCandidateQ y)

theorem pair_qm_square_maps_to_candidate (x : AspisR1S9PairCallerStepV1.field.QM31) :
    mapResult pairToCandidateQ (AspisR1S9PairCallerStepV1.field.QM31.square x) =
      AspisR1S9CandidateHelperV1.field.QM31.square (pairToCandidateQ x) := by
  apply mapResult_injective AspisR1S9CandidateHelperV1.toP6Q candidateToP6_injective_Q
  calc
    mapResult AspisR1S9CandidateHelperV1.toP6Q (mapResult pairToCandidateQ (AspisR1S9PairCallerStepV1.field.QM31.square x)) =
        mapResult AspisR1S9PairCallerStepV1.toP6Q (AspisR1S9PairCallerStepV1.field.QM31.square x) := by
          cases AspisR1S9PairCallerStepV1.field.QM31.square x <;>
            simp [mapResult, pairToCandidateQ, AspisR1S9CandidateHelperV1.toP6Q_fromP6Q]
    _ = @AspisR1S9HelperP6.FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9PairCallerStepV1.toP6Q x) := AspisR1S9PairCallerStepOperationBridgeV1.map_qm_square x
    _ = mapResult AspisR1S9CandidateHelperV1.toP6Q (AspisR1S9CandidateHelperV1.field.QM31.square (pairToCandidateQ x)) := by
          symm
          change AspisR1S9CandidateHelperBridgeV1.mapResult AspisR1S9CandidateHelperV1.toP6Q
            (AspisR1S9CandidateHelperV1.field.QM31.square (pairToCandidateQ x)) = _
          exact AspisR1S9CandidateHelperBridgeV1.map_qm_square (pairToCandidateQ x)

theorem pair_wide_add_maps_to_candidate (x y : AspisR1S9PairCallerStepV1.field.WideExact) :
    mapResult pairToCandidateW (AspisR1S9PairCallerStepV1.field.WideExact.add x y) =
      AspisR1S9CandidateHelperV1.field.WideExact.add (pairToCandidateW x) (pairToCandidateW y) := by
  apply mapResult_injective AspisR1S9CandidateHelperV1.toP6W candidateToP6_injective_W
  calc
    mapResult AspisR1S9CandidateHelperV1.toP6W (mapResult pairToCandidateW (AspisR1S9PairCallerStepV1.field.WideExact.add x y)) =
        mapResult AspisR1S9PairCallerStepV1.toP6W (AspisR1S9PairCallerStepV1.field.WideExact.add x y) := by
          cases AspisR1S9PairCallerStepV1.field.WideExact.add x y <;>
            simp [mapResult, pairToCandidateW, AspisR1S9CandidateHelperV1.toP6W_fromP6W]
    _ = @AspisR1S9HelperP6.FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9PairCallerStepV1.toP6W x) (AspisR1S9PairCallerStepV1.toP6W y) :=
      AspisR1S9PairCallerStepOperationBridgeV1.map_wide_add x y
    _ = mapResult AspisR1S9CandidateHelperV1.toP6W (AspisR1S9CandidateHelperV1.field.WideExact.add (pairToCandidateW x)
          (pairToCandidateW y)) := by
          symm
          change AspisR1S9CandidateHelperBridgeV1.mapResult AspisR1S9CandidateHelperV1.toP6W
            (AspisR1S9CandidateHelperV1.field.WideExact.add (pairToCandidateW x) (pairToCandidateW y)) = _
          exact AspisR1S9CandidateHelperBridgeV1.map_wide_add (pairToCandidateW x) (pairToCandidateW y)

theorem pair_wide_mul_maps_to_candidate (x y : AspisR1S9PairCallerStepV1.field.WideExact) :
    mapResult pairToCandidateW (AspisR1S9PairCallerStepV1.field.WideExact.mul x y) =
      AspisR1S9CandidateHelperV1.field.WideExact.mul (pairToCandidateW x) (pairToCandidateW y) := by
  apply mapResult_injective AspisR1S9CandidateHelperV1.toP6W candidateToP6_injective_W
  calc
    mapResult AspisR1S9CandidateHelperV1.toP6W (mapResult pairToCandidateW (AspisR1S9PairCallerStepV1.field.WideExact.mul x y)) =
        mapResult AspisR1S9PairCallerStepV1.toP6W (AspisR1S9PairCallerStepV1.field.WideExact.mul x y) := by
          cases AspisR1S9PairCallerStepV1.field.WideExact.mul x y <;>
            simp [mapResult, pairToCandidateW, AspisR1S9CandidateHelperV1.toP6W_fromP6W]
    _ = @AspisR1S9HelperP6.FieldOps.wideMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9PairCallerStepV1.toP6W x) (AspisR1S9PairCallerStepV1.toP6W y) :=
      AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul x y
    _ = mapResult AspisR1S9CandidateHelperV1.toP6W (AspisR1S9CandidateHelperV1.field.WideExact.mul (pairToCandidateW x)
          (pairToCandidateW y)) := by
          symm
          change AspisR1S9CandidateHelperBridgeV1.mapResult AspisR1S9CandidateHelperV1.toP6W
            (AspisR1S9CandidateHelperV1.field.WideExact.mul (pairToCandidateW x) (pairToCandidateW y)) = _
          exact AspisR1S9CandidateHelperBridgeV1.map_wide_mul (pairToCandidateW x) (pairToCandidateW y)

theorem pair_wide_mul_m31_maps_to_candidate (x : AspisR1S9PairCallerStepV1.field.WideExact) (y : AspisR1S9PairCallerStepV1.field.M31) :
    mapResult pairToCandidateW (AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 x y) =
      AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 (pairToCandidateW x) (pairToCandidateM y) := by
  apply mapResult_injective AspisR1S9CandidateHelperV1.toP6W candidateToP6_injective_W
  calc
    mapResult AspisR1S9CandidateHelperV1.toP6W (mapResult pairToCandidateW (AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 x y)) =
        mapResult AspisR1S9PairCallerStepV1.toP6W (AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 x y) := by
          cases AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 x y <;>
            simp [mapResult, pairToCandidateW, AspisR1S9CandidateHelperV1.toP6W_fromP6W]
    _ = @AspisR1S9HelperP6.FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9PairCallerStepV1.toP6W x) (AspisR1S9PairCallerStepV1.toP6M y) :=
      AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul_m31 x y
    _ = mapResult AspisR1S9CandidateHelperV1.toP6W (AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 (pairToCandidateW x)
          (pairToCandidateM y)) := by
          symm
          change AspisR1S9CandidateHelperBridgeV1.mapResult AspisR1S9CandidateHelperV1.toP6W
            (AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 (pairToCandidateW x) (pairToCandidateM y)) = _
          exact AspisR1S9CandidateHelperBridgeV1.map_wide_mul_m31 (pairToCandidateW x) (pairToCandidateM y)

theorem pair_wide_mul_qm31_maps_to_candidate
    (x : AspisR1S9PairCallerStepV1.field.WideExact) (y : AspisR1S9PairCallerStepV1.field.QM31) :
    mapResult pairToCandidateW (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x y) =
      AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 (pairToCandidateW x) (pairToCandidateQ y) := by
  apply mapResult_injective AspisR1S9CandidateHelperV1.toP6W candidateToP6_injective_W
  calc
    mapResult AspisR1S9CandidateHelperV1.toP6W (mapResult pairToCandidateW (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x y)) =
        mapResult AspisR1S9PairCallerStepV1.toP6W (AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x y) := by
          cases AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x y <;>
            simp [mapResult, pairToCandidateW, AspisR1S9CandidateHelperV1.toP6W_fromP6W]
    _ = @AspisR1S9HelperP6.FieldOps.wideMulQM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
          (AspisR1S9PairCallerStepV1.toP6W x) (AspisR1S9PairCallerStepV1.toP6Q y) :=
      AspisR1S9PairCallerStepOperationBridgeV1.map_wide_mul_qm31 x y
    _ = mapResult AspisR1S9CandidateHelperV1.toP6W (AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 (pairToCandidateW x)
          (pairToCandidateQ y)) := by
          symm
          change AspisR1S9CandidateHelperBridgeV1.mapResult AspisR1S9CandidateHelperV1.toP6W
            (AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 (pairToCandidateW x) (pairToCandidateQ y)) = _
          exact AspisR1S9CandidateHelperBridgeV1.map_wide_mul_qm31 (pairToCandidateW x) (pairToCandidateQ y)

#print axioms pair_qm_mul_maps_to_candidate
#print axioms pair_qm_square_maps_to_candidate
#print axioms pair_wide_add_maps_to_candidate
#print axioms pair_wide_mul_maps_to_candidate
#print axioms pair_wide_mul_m31_maps_to_candidate
#print axioms pair_wide_mul_qm31_maps_to_candidate

end AspisR1S9PairCallerCandidateMapV1
