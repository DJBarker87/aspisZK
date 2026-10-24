import S9ActualPairScalarFactorShortV1
import S9PairCallerScalarFactorFoldTransportV1
import S9PairArrayUpdateCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairOldCarrierScalarV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31
abbrev OW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev OQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev mapArray := @AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
abbrev mapResult := @AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
abbrev toHelperQ := AspisR1S9ActualPairQMHelperTransportV1.toHelperQ
abbrev toHelperW := AspisR1S9ActualPairWideHelperTransportV1.toHelperW
def toOldQ (x : Q) : OQ := AspisR1S9PairCallerStepV1.fromP6Q (toHelperQ x)
def toOldW (x : W) : OW := AspisR1S9PairCallerStepV1.fromP6W (toHelperW x)

theorem toP6Q_toOldQ (x : Q) : AspisR1S9PairCallerStepV1.toP6Q (toOldQ x) = toHelperQ x :=
  AspisR1S9PairCallerStepV1.toP6Q_fromP6Q _
theorem toP6W_toOldW (x : W) : AspisR1S9PairCallerStepV1.toP6W (toOldW x) = toHelperW x :=
  AspisR1S9PairCallerStepV1.toP6W_fromP6W _

theorem map_array_comp {A B C : Type} {n : Usize}
    (f : A → B) (g : B → C) (a : Array A n) :
    mapArray g (mapArray f a) = mapArray (g ∘ f) a := by
  cases a
  simp [AspisR1S9CandidateFoldMapPrimitivesV1.mapArray,List.map_map,Function.comp]

theorem mapped_q_array (f : Array Q 4#usize) :
    mapArray AspisR1S9PairCallerStepV1.toP6Q (mapArray toOldQ f) = mapArray toHelperQ f := by
  rw [map_array_comp]
  congr 1

theorem mapped_w_array (p : Array W 4#usize) :
    mapArray AspisR1S9PairCallerStepV1.toP6W (mapArray toOldW p) = mapArray toHelperW p := by
  rw [map_array_comp]
  congr 1

private theorem inverse_map_success {A B : Type} (f : A → B) (g : B → A)
    (hinv : ∀ a, g (f a) = a) (r : Result A) (b : B)
    (h : mapResult f r = .ok b) : r = .ok (g b) := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok a =>
    have he : f a = b := Result.ok.inj h
    rw [←he,hinv]

/-- Reuse of the checked old scalar control-flow transport is justified by
its complete Result equality and inverse carrier maps. This derives the old
helper success from the same actual32 success, not an independent premise. -/
theorem actual_scalar_success_to_old (f : Array Q 4#usize) (p : Array W 4#usize)
    (out : W) (hp : AspisR1S9ActualPairScalarCallbackV1.GoodArray p)
    (h : weights.Weights.scalar_factor f p = .ok out) :
    AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
      (mapArray toOldQ f) (mapArray toOldW p) = .ok (toOldW out) := by
  have hs := (AspisR1S9ActualPairScalarFactorShortV1.actual_scalar_factor_success_maps f p out hp h).2
  have hold := AspisR1S9PairCallerScalarFactorFoldTransportV1.pair_scalar_factor_maps_to_p6
    (mapArray toOldQ f) (mapArray toOldW p)
  change mapResult AspisR1S9PairCallerStepV1.toP6W
    (AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor (mapArray toOldQ f) (mapArray toOldW p)) =
    @AspisR1S9HelperP6.weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (mapArray AspisR1S9PairCallerStepV1.toP6Q (mapArray toOldQ f))
      (mapArray AspisR1S9PairCallerStepV1.toP6W (mapArray toOldW p)) at hold
  rw [mapped_q_array,mapped_w_array] at hold
  change @AspisR1S9HelperP6.weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
    (mapArray toHelperQ f) (mapArray toHelperW p) = .ok (toHelperW out) at hs
  rw [hs] at hold
  exact inverse_map_success AspisR1S9PairCallerStepV1.toP6W
    AspisR1S9PairCallerStepV1.fromP6W AspisR1S9PairCallerStepV1.fromP6W_toP6W _ _ hold
#print axioms toP6Q_toOldQ
#print axioms toP6W_toOldW
#print axioms mapped_q_array
#print axioms mapped_w_array
#print axioms actual_scalar_success_to_old
end AspisR1S9ActualPairOldCarrierScalarV1
