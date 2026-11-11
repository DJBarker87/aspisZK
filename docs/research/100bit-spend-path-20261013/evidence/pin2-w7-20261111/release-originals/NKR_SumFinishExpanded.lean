import NKR_SumFinishAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishExpanded
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode K)
open NKR_SumFinishData
open NKR_SumFinishMeaning

def coordinates (b : Fin 9) : List (Fin 30) := List.ofFn (batchCoordinate b)

/-- Each concretebatch has at most4symbolic products. This expands only its
array/index shape;no field operation or large generated recurrence unfolds. -/
theorem batch_value (xs lows : Fin 30 → NQ) (b : Fin 9) :
 delta xs lows b=((coordinates b).map (fun c=>decode (xs c)*decode (lows c))).sum := by
 fin_cases b <;> rfl

theorem partition : NKR_SumFinishFold.order.flatMap coordinates=List.finRange 30 := by decide

theorem coordinate_group (b : Fin 9) (c : Fin 30) (hc : c∈coordinates b) : group c=batchGroup b := by
 obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
 exact batch_same_group b i

theorem sum_flatMap {A B : Type} (f : A → List B) (v : B → K) (xs : List A) :
 ((xs.flatMap f).map v).sum=(xs.map (fun a=>((f a).map v).sum)).sum := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,List.map_cons,List.sum_cons]

/-- All nine batched group sums equal the unbatched30-coordinate definition.
The group partition is a30-element index fact,not arithmetic enumeration. -/
theorem group_value (xs lows : Fin 30 → NQ) (g : Fin 4) :
 (NKR_SumFinishFold.order.map (fun b=>if batchGroup b=g then delta xs lows b else 0)).sum=
 ((List.finRange 30).map (fun c=>if group c=g then decode (xs c)*decode (lows c) else 0)).sum := by
 rw [←partition,sum_flatMap]
 apply congrArg List.sum
 apply List.map_congr_left
 intro b hb
 rw [batch_value]
 by_cases same : batchGroup b=g
 · simp only [if_pos same]
   apply congrArg List.sum
   apply List.map_congr_left
   intro c hc
   rw [coordinate_group b c hc,if_pos same]
 · simp only [if_neg same]
   symm
   have zero : ((coordinates b).map (fun c=>if group c=g then decode (xs c)*decode (lows c) else 0))=
    (coordinates b).map (fun _=>0) := by
    apply List.map_congr_left
    intro c hc
    rw [coordinate_group b c hc,if_neg same]
   rw [zero]
   simp

#print axioms batch_value
#print axioms partition
#print axioms coordinate_group
#print axioms sum_flatMap
#print axioms group_value
end AspisR1.NKR_SumFinishExpanded
end
