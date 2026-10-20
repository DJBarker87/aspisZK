import S3OptimizedInactiveTableBridge
import S3OptimizedPairAccumulationBridge

set_option autoImplicit false
namespace AspisR1.S3OptimizedPairLoopSemantics

open AspisR1.S3S9CurrentSourceModel
open AspisR1.S3OptimizedPairAccumulationBridge

theorem addFold_eq_sum {α E : Type} [AddCommMonoid E] (xs : List α)
    (f : α → E) (init : E) :
    xs.foldl (fun acc x => acc + f x) init = init + (xs.map f).sum := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, ih, add_assoc]

def coeffStep {E : Type} [Add E]
    (coeff : Fin 64 → E) (acc : Fin 12 → E) (j : Fin 64) : Fin 12 → E :=
  fun g => if groupAt j = g then acc g + coeff j else acc g

def coefficientLoop {E : Type} [Add E]
    (coeff : Fin 64 → E) (js : List (Fin 64)) (init : Fin 12 → E) : Fin 12 → E :=
  js.foldl (coeffStep coeff) init

theorem coefficientLoop_spec {E : Type} [AddCommMonoid E]
    (coeff : Fin 64 → E) (js : List (Fin 64)) (init : Fin 12 → E) (g : Fin 12) :
    coefficientLoop coeff js init g =
      init g + (js.map fun j => if groupAt j = g then coeff j else 0).sum := by
  induction js generalizing init with
  | nil => simp [coefficientLoop]
  | cons j js ih =>
      by_cases h : groupAt j = g
      · change coefficientLoop coeff js (coeffStep coeff init j) g = _
        rw [ih]
        simp [coeffStep, h, add_assoc]
      · change coefficientLoop coeff js (coeffStep coeff init j) g = _
        rw [ih]
        simp [coeffStep, h]

theorem coefficientLoop_finRange {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (g : Fin 12) :
    coefficientLoop coeff (List.finRange 64) (fun _ => 0) g =
      coefficientsAfterLoop coeff g := by
  rw [coefficientLoop_spec]
  unfold coefficientsAfterLoop
  rw [← List.sum_toFinset (fun j => if groupAt j = g then coeff j else 0)
    (List.nodup_finRange 64)]
  rw [List.toFinset_finRange]
  simp

def weightStep {E : Type} [Add E]
    (low : Fin 16 → E) (g : Fin 12) (acc : E) (s : Fin 16) : E :=
  if inactiveAtGroup g s then acc + low s else acc

def weightLoop {E : Type} [AddCommMonoid E]
    (low : Fin 16 → E) (g : Fin 12) : E :=
  (List.finRange 16).foldl (weightStep low g) 0

theorem weightLoop_spec {E : Type} [AddCommMonoid E]
    (low : Fin 16 → E) (g : Fin 12) :
    weightLoop low g = weightAfterLoop low g := by
  unfold weightLoop weightAfterLoop
  have hfold : (List.finRange 16).foldl (weightStep low g) 0 =
      ((List.finRange 16).map (fun s => if inactiveAtGroup g s then low s else 0)).sum := by
    have hadd := addFold_eq_sum (List.finRange 16)
      (fun s => if inactiveAtGroup g s then low s else 0) (0 : E)
    have hstep : (List.finRange 16).foldl (weightStep low g) 0 =
        (List.finRange 16).foldl
          (fun acc s => acc + if inactiveAtGroup g s then low s else 0) 0 := by
      induction (List.finRange 16) with
      | nil => rfl
      | cons s ss ih =>
          simp only [List.foldl_cons]
          rw [ih]
          by_cases h : inactiveAtGroup g s <;> simp [weightStep, h]
    rw [hstep, hadd]
  rw [hfold]
  rw [← List.sum_toFinset (fun s => if inactiveAtGroup g s then low s else 0)
    (List.nodup_finRange 16)]
  rw [List.toFinset_finRange]

def outerStep {E : Type} [AddCommMonoid E] [Mul E]
    (coeff : Fin 12 → E) (weight : Fin 12 → E) (acc : E) (g : Fin 12) : E :=
  acc + coeff g * weight g

def outerLoop {E : Type} [AddCommMonoid E] [Mul E]
    (coeff weight : Fin 12 → E) : E :=
  (List.finRange 12).foldl (outerStep coeff weight) 0

theorem outerLoop_spec {E : Type} [CommSemiring E]
    (coeff weight : Fin 12 → E) :
    outerLoop coeff weight = ∑ g : Fin 12, coeff g * weight g := by
  unfold outerLoop
  rw [addFold_eq_sum (List.finRange 12) (fun g => coeff g * weight g) (0 : E)]
  simp only [zero_add]
  rw [← List.sum_toFinset (fun g => coeff g * weight g) (List.nodup_finRange 12)]
  rw [List.toFinset_finRange]

def threeLoopModel {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E) : E :=
  outerLoop (fun g => coefficientLoop coeff (List.finRange 64) (fun _ => 0) g)
    (fun g => weightLoop low g)

theorem threeLoopModel_eq_groupedPair {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E) :
    threeLoopModel coeff low = groupedPair coeff low groupAt inactiveAtGroup := by
  simp [threeLoopModel, outerLoop_spec, coefficientLoop_finRange, weightLoop_spec,
    groupedPair]

theorem threeLoopModel_eq_actualRowFunctional {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E) :
    threeLoopModel coeff low = ungroupedPair coeff low inactiveAtSource := by
  rw [threeLoopModel_eq_groupedPair]
  exact s3_grouped_pair_exact coeff low

#print axioms coefficientLoop_spec
#print axioms threeLoopModel_eq_groupedPair
#print axioms threeLoopModel_eq_actualRowFunctional
end AspisR1.S3OptimizedPairLoopSemantics
