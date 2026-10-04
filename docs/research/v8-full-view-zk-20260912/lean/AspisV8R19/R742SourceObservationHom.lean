import AspisV8R19.R738JointObservationModel
import AspisV8R19.R740SparsePointObservation

/-! Ring-map naturality for the ordinary source observation ingredients.
No execution, rank, oracle distribution, or security conclusion is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.R742SourceObservationHom
open AspisV8R16 AspisV8R17 AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R740SparsePointObservation
open scoped BigOperators
noncomputable section
variable {F K : Type*} [CommRing F] [CommRing K]

lemma sourceGather_powers (half : F) (w : Nat → F) (i : Nat) :
    sourceGather half w i =
      (((indexLoop 10 i 0).getD []).map (fun e => half^e.2*w e.1)).sum := by
  unfold sourceGather
  rw [show weightedIndexLoop half 10 i 0 1 =
      (indexLoop 10 i 0).map (List.map (fun e => (e.1,half^e.2))) by
        simpa using weightedIndexLoop_powers half 10 i 0]
  cases indexLoop 10 i 0 <;> simp [List.map_map,Function.comp_def]

lemma map_sourceGather (f : F →+* K) (half : F) (w : Nat → F) (i : Nat) :
    f (sourceGather half w i) = sourceGather (f half) (fun j => f (w j)) i := by
  simp only [sourceGather_powers, map_list_sum, List.map_map, Function.comp_def, map_mul, map_pow]

lemma map_sourcePointBasis (f : F →+* K) (point : Fin 10 → F) (i : Nat) :
    f (sourcePointBasis point i) = sourcePointBasis (fun j => f (point j)) i := by
  simp only [sourcePointBasis,sourceMultilinearFactors,List.prod_ofFn]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> simp only [map_sub,map_one]

lemma map_points (f : F →+* K) (z : Fin 10 → F) (p : Fin 3) (i : Fin 10) :
    f (SourceStatementPoints.points z p i) =
      SourceStatementPoints.points (fun j => f (z j)) p i := by
  have hc : f (ResidualModel.carry z i) = ResidualModel.carry (fun j => f (z j)) i := by
    unfold ResidualModel.carry
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j _
    split_ifs <;> simp only [map_one]
  rw [SourceStatementPoints.points_eq,SourceStatementPoints.points_eq]
  simp only [ResidualModel.point]
  split_ifs <;> simp only [map_add,map_sub,map_mul,map_ofNat,map_one,hc]

lemma map_transportDual (f : F →+* K) (w : Fin 1024 → F) (i : Fin 1024) :
    f (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order w i) =
      transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
        (fun j => f (w j)) i := by
  unfold transportDual
  split_ifs <;> simp only [map_sub]

lemma map_extendFin1024 (f : F →+* K) (w : Fin 1024 → F) (i : Nat) :
    f (extendFin1024 w i) = extendFin1024 (fun j => f (w j)) i := by
  unfold extendFin1024
  split <;> simp

lemma map_sourceChordTranspose (f : F →+* K) (half a b c : F) (w : Nat → F) (i : Nat) :
    f (sourceChordTranspose half w a b c i) =
      sourceChordTranspose (f half) (fun j => f (w j)) (f a) (f b) (f c) i := by
  have hz (n : Nat) (v : Nat → F) (j : Nat) :
      f (zeroExtend n v j) = zeroExtend n (fun j => f (v j)) j := by
    unfold zeroExtend
    split_ifs <;> simp only [map_zero]
  unfold sourceChordTranspose interleave
  split <;> simp only [chordDualEven,chordDualOdd,map_add,map_sub,map_mul,
    map_sourceGather,hz]

lemma map_sourceQuotientWeights (f : F →+* K) (half a b c tau : F)
    (w : Nat → F) (structured : Bool) (i : Nat) :
    f (sourceQuotientWeights half w a b c tau structured i) =
      sourceQuotientWeights (f half) (fun j => f (w j)) (f a) (f b) (f c)
        (f tau) structured i := by
  cases structured <;>
    simp only [sourceQuotientWeights,sourceImageUpdates_apply,Bool.false_eq_true,
      Bool.true_eq,if_false,if_true,map_sourceChordTranspose,map_add,map_sub,map_mul,map_pow]
  all_goals split_ifs <;> first | rfl | simp only [map_zero,map_mul,map_pow]

lemma map_rawOrdinaryOriginal (f : F →+* K) (z : Fin 10 → F) (kappa : F) (i : Fin 1024) :
    f (rawOrdinaryOriginal z kappa i) =
      rawOrdinaryOriginal (fun j => f (z j)) (f kappa) i := by
  have hp (p : Fin 3) : (fun j => f (SourceStatementPoints.points z p j)) =
      SourceStatementPoints.points (fun j => f (z j)) p := by
    funext j; exact map_points f z p j
  by_cases hi : i ∈ TwoSwapSourceTable.inactive <;>
    simp only [rawOrdinaryOriginal,sourceOriginalWeight_eq,Bool.false_eq_true,
      if_false,map_add,map_sub,map_mul,map_pow,map_zero,map_one,
      map_sourcePointBasis,hp,hi,if_true]

lemma map_rawOrdinaryWeight (f : F →+* K) (half a b c kappa tau : F)
    (z : Fin 10 → F) (i : Nat) :
    f (rawOrdinaryWeight half a b c kappa tau z i) =
      rawOrdinaryWeight (f half) (f a) (f b) (f c) (f kappa) (f tau)
        (fun j => f (z j)) i := by
  unfold rawOrdinaryWeight
  rw [map_sourceQuotientWeights]
  congr 1
  funext j
  simp only [map_extendFin1024,map_transportDual,map_rawOrdinaryOriginal]

lemma map_pointWeight (f : F →+* K) (half a b c : F) (point : Fin 10 → F) (i : Nat) :
    f (pointWeight half a b c point i) =
      pointWeight (f half) (f a) (f b) (f c) (fun j => f (point j)) i := by
  unfold pointWeight
  rw [map_sourceChordTranspose]
  congr 1
  funext j
  simp only [map_extendFin1024,map_transportDual,map_sourcePointBasis]

#print axioms sourceGather_powers
#print axioms map_sourceGather
#print axioms map_sourcePointBasis
#print axioms map_points
#print axioms map_transportDual
#print axioms map_extendFin1024
#print axioms map_sourceChordTranspose
#print axioms map_sourceQuotientWeights
#print axioms map_rawOrdinaryOriginal
#print axioms map_rawOrdinaryWeight
#print axioms map_pointWeight
end
end AspisV8R19.R742SourceObservationHom
