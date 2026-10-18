import PoseidonMap

/-! Extend the maintained scalar naturality lemmas only at the three pair
boundaries used by the projected caller. All round and matrix functions remain
opaque; constant and ordered-fold transport reuse PoseidonMap. -/
set_option autoImplicit false
namespace AspisR1.PoseidonPairMap
open R0P AspisR1.PoseidonMap
variable {K L : Type} [Field K] [Field L] (f : K →+* L)

theorem map_poseidonLeadingPair (state absorption : State K) :
    mapState f (poseidonLeadingPair state absorption) =
      poseidonLeadingPair (mapState f state) (mapState f absorption) := by
  unfold poseidonLeadingPair
  rw [map_poseidonFullRound,map_poseidonFullRound,map_poseidonExternalLinear]
  have hinput : mapState f (fun lane =>
      if lane.val < 8 then state lane + absorption lane else state lane) =
      (fun lane => if lane.val < 8 then
        mapState f state lane + mapState f absorption lane else mapState f state lane) := by
    funext lane
    by_cases h : lane.val < 8 <;> simp only [mapState,h,ite_true,ite_false,map_add]
  rw [hinput]
  have hc0 : mapState f (poseidonExternalInitial (K := K) 0) =
      poseidonExternalInitial (K := L) 0 := funext (map_poseidonExternalInitial f 0)
  have hc1 : mapState f (poseidonExternalInitial (K := K) 1) =
      poseidonExternalInitial (K := L) 1 := funext (map_poseidonExternalInitial f 1)
  rw [hc0,hc1]

theorem map_poseidonInterpolatedFullPair (state low : State K) :
    mapState f (poseidonInterpolatedFullPair state low) =
      poseidonInterpolatedFullPair (mapState f state) (mapState f low) := by
  unfold poseidonInterpolatedFullPair
  rw [map_poseidonFullRound,map_poseidonFullRound]
  have hconstant (a b c : Fin 4) :
      mapState f (fun lane =>
        (low 1 * poseidonExternalInitial a lane + low 9 * poseidonExternalFinal b lane) +
          low 10 * poseidonExternalFinal c lane) =
      (fun lane =>
        (mapState f low 1 * poseidonExternalInitial a lane +
          mapState f low 9 * poseidonExternalFinal b lane) +
          mapState f low 10 * poseidonExternalFinal c lane) := by
    funext lane
    simp only [mapState,map_add,map_mul,map_poseidonExternalInitial,map_poseidonExternalFinal]
  rw [hconstant 2 0 2,hconstant 3 1 3]

theorem map_poseidonInterpolatedInternalPair (state low : State K) :
    mapState f (poseidonInterpolatedInternalPair state low) =
      poseidonInterpolatedInternalPair (mapState f state) (mapState f low) := by
  unfold poseidonInterpolatedInternalPair
  rw [map_poseidonInternalRound,map_poseidonInternalRound]
  simp only [map_foldl_add,List.map_ofFn,Function.comp_def,map_zero,map_mul,
    map_poseidonInternalConstants,mapState]

#print axioms map_poseidonLeadingPair
#print axioms map_poseidonInterpolatedFullPair
#print axioms map_poseidonInterpolatedInternalPair
end AspisR1.PoseidonPairMap
