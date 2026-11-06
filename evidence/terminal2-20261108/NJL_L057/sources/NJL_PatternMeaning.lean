import NJB_PatternReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PatternMeaning
open FIv_NativeValue (K)
def dot (terms : Fin 14 → K) (weights : Fin 26 → K) (g : Fin 4) : K :=
 ((NJB_PatternReference.coordinates g).map (fun c=>terms (NJB_PatternReference.pattern c)*weights c)).sum
/-- Symbolic sparse four-group accumulation, no concrete field recurrence. -/
theorem prefix (terms : Fin 14 → K) (weights : Fin 26 → K) (gs : List (Fin 4)) (before : Fin 4 → K) (j : Fin 4) :
 (gs.foldl (fun s g=>NJB_PatternReference.groupModel terms weights g s) before) j=
 before j+(gs.map (fun g=>if g=j then dot terms weights g else 0)).sum := by
 induction gs generalizing before with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons,ih]
  by_cases same : g=j
  · subst g
    simp only [NJB_PatternReference.groupModel,if_true,List.map_cons,List.sum_cons,dot]
    ring
  · simp only [NJB_PatternReference.groupModel,if_neg same,List.map_cons,List.sum_cons,zero_add]
/-- Complete four-cell basis meaning at every group, including arbitrary
initial values. This is the predecessor model's sparse weighted contribution. -/
theorem value (terms : Fin 14 → K) (weights : Fin 26 → K) (before : Fin 4 → K) (j : Fin 4) :
 NJB_PatternReference.model terms weights before j=before j+dot terms weights j := by
 change ((List.ofFn (fun g : Fin 4=>g)).foldl (fun s g=>NJB_PatternReference.groupModel terms weights g s) before) j=_
 rw [prefix,List.map_ofFn,List.sum_ofFn]
 simp
#print axioms prefix
#print axioms value
end AspisR1.NJL_PatternMeaning
end
