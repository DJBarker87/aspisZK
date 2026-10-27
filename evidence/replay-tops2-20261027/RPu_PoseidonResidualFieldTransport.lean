import RPu_PoseidonPairMap
import RPu_PathFamilyFieldTransport

/-! Transport the existing unrandomized Poseidon family, preserving its
three branches and ordered selector folds. This does not replace the relation
or claim that a packed zero is an unpacked zero. -/
set_option autoImplicit false
namespace AspisR1.PoseidonResidualFieldTransport
open R0P
open AspisR1.PoseidonMap
open AspisR1.PoseidonPairMap
open AspisR1.ValueFamilyFieldTransport (mapOpenings)
variable {K L : Type} [Field K] [Field L] (f : K →+* L)

theorem map_packingFormula (i u : K) (values : Fin 4 → K) :
    f (poseidonPackingFormula i u values) =
      poseidonPackingFormula (f i) (f u) (fun j => f (values j)) := by
  simp only [poseidonPackingFormula,map_add,map_mul]

theorem map_scalarResidual (o : Openings K) (block : K)
    (low : Fin 16 → K) (lane : Fin 16) :
    f (poseidonScalarResidual o block low lane) =
      poseidonScalarResidual (mapOpenings f o) (f block) (mapState f low) lane := by
  have hfull : f (([1,9,10] : List (Fin 16)).foldl (fun sum row => sum + low row) 0) =
      ([1,9,10] : List (Fin 16)).foldl (fun sum row => sum + f (low row)) 0 := by
    simp only [List.foldl_cons,List.foldl_nil,map_add,map_zero]
  have hinternal : f ((List.ofFn (fun i : Fin 7 => low ⟨i.val+2,by omega⟩)).foldl (·+·) 0) =
      (List.ofFn (fun i : Fin 7 => f (low ⟨i.val+2,by omega⟩))).foldl (·+·) 0 := by
    simp only [map_foldl_add,List.map_ofFn,Function.comp_def,map_zero]
  have hleading : f (poseidonLeadingPair o.z o.xor12 lane) =
      poseidonLeadingPair (mapState f o.z) (mapState f o.xor12) lane :=
    congrFun (map_poseidonLeadingPair f o.z o.xor12) lane
  have hfullPair : f (poseidonInterpolatedFullPair o.z low lane) =
      poseidonInterpolatedFullPair (mapState f o.z) (mapState f low) lane :=
    congrFun (map_poseidonInterpolatedFullPair f o.z low) lane
  have hinternalPair : f (poseidonInterpolatedInternalPair o.z low lane) =
      poseidonInterpolatedInternalPair (mapState f o.z) (mapState f low) lane :=
    congrFun (map_poseidonInterpolatedInternalPair f o.z low) lane
  unfold poseidonScalarResidual
  simp only [map_mul,map_add,map_sub,map_zero,hfull,hinternal,
    hleading,hfullPair,hinternalPair,mapOpenings,mapState]
  all_goals rfl

theorem map_packed_scalarResidual (o : Openings K) (block i u : K)
    (low : Fin 16 → K) (lanes : Fin 4 → Fin 16) :
    f (poseidonPackingFormula i u (fun j => poseidonScalarResidual o block low (lanes j))) =
      poseidonPackingFormula (f i) (f u) (fun j =>
        poseidonScalarResidual (mapOpenings f o) (f block) (mapState f low) (lanes j)) := by
  simp only [map_packingFormula,map_scalarResidual]

theorem map_family (pub : Public K) (pub' : Public L)
    (o : Openings K) (sel : Sel K) :
    ((poseidonScalarFamily (K := K)).residuals pub o sel).map f =
      (poseidonScalarFamily (K := L)).residuals pub' (mapOpenings f o)
        (fun i => f (sel i)) := by
  have hlow : mapState f (g2Low sel) = g2Low (fun i => f (sel i)) := by
    funext i
    exact AspisR1.PathFamilyFieldTransport.map_low f sel i
  simp only [poseidonScalarFamily,List.map_ofFn,Function.comp_def]
  congr 1
  funext lane
  rw [map_scalarResidual,AspisR1.PathFamilyFieldTransport.map_sumHigh,hlow]

#print axioms map_packingFormula
#print axioms map_scalarResidual
#print axioms map_packed_scalarResidual
#print axioms map_family
end AspisR1.PoseidonResidualFieldTransport
