import NKR_SumFinishMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishAlgebra
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open NKR_SumFinishData
open NKR_SumFinishMeaning

/-- Symbolic accumulation over arbitrary batch lists. No concrete recurrence
or field product is reduced;the shape is a four-cell additive frame. -/
theorem values (tags weights lows : Fin 30 → NQ) (bs : List (Fin 9)) (before : ModelState) (j : Fin 4) :
 (bs.foldl (fun state b=>stepModel tags weights lows b state) before).1 j=
 before.1 j+(bs.map (fun b=>if batchGroup b=j then delta tags lows b else 0)).sum := by
 induction bs generalizing before with
 | nil => simp
 | cons b bs ih =>
  rw [List.foldl_cons,ih]
  by_cases same : batchGroup b=j
  · simp only [stepModel,NJB_StateUpdates.addModel,if_pos same,List.map_cons,List.sum_cons]
    rw [same]
    ring
  · simp only [stepModel,NJB_StateUpdates.addModel,if_neg same,List.map_cons,List.sum_cons,zero_add]

theorem weights (tags weights lows : Fin 30 → NQ) (bs : List (Fin 9)) (before : ModelState) (j : Fin 4) :
 (bs.foldl (fun state b=>stepModel tags weights lows b state) before).2 j=
 before.2 j+(bs.map (fun b=>if batchGroup b=j then delta weights lows b else 0)).sum := by
 induction bs generalizing before with
 | nil => simp
 | cons b bs ih =>
  rw [List.foldl_cons,ih]
  by_cases same : batchGroup b=j
  · simp only [stepModel,NJB_StateUpdates.addModel,if_pos same,List.map_cons,List.sum_cons]
    rw [same]
    ring
  · simp only [stepModel,NJB_StateUpdates.addModel,if_neg same,List.map_cons,List.sum_cons,zero_add]

#print axioms values
#print axioms weights
end AspisR1.NKR_SumFinishAlgebra
end
