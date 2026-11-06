import NKR_SumFinishPattern
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumPatternMeaning
open FIv_NativeValue (K)
open NKR_SumFinishData

theorem source (scratch : Fin 103 → K) (lows : Fin 16 → K) (cs : List (Fin 43))
 (before : Fin 26 → K) (j : Fin 26) :
 (cs.foldl (fun state c=>NKR_SumFinishPattern.modelStep scratch lows c state) before) j=
 before j+(cs.map (fun c=>if pOut c=j then scratch (NKR_SumFinishPattern.scratchIndex c)*lows (pLow c) else 0)).sum := by
 induction cs generalizing before with
 | nil => simp
 | cons c cs ih =>
  rw [List.foldl_cons,ih]
  by_cases same : pOut c=j
  · simp only [NKR_SumFinishPattern.modelStep,NJB_StateUpdates.addModel,if_pos same,List.map_cons,List.sum_cons]
    rw [same]
    ring
  · simp only [NKR_SumFinishPattern.modelStep,NJB_StateUpdates.addModel,if_neg same,List.map_cons,List.sum_cons,zero_add]

#print axioms source
end AspisR1.NKR_SumPatternMeaning
end
