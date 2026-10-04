import AspisV8R19.TwoSwapSourceWeights
import AspisV8R19.SourceGConstant

/-! Ordered G scatter and both original-weight channels for the two-swap
profile. Only generic list-update and final-coin facts are reused. The other
270 coins, the point arrays and all challenge scalars remain arbitrary. -/
set_option autoImplicit false
namespace AspisR19.TwoSwapSourceG
open AspisV8R17 TwoSwapSourceTable TwoSwapSourceWeights
noncomputable section
variable {F : Type*} [CommRing F]

def coinIndex (i : Fin 271) : Fin 1024 := ⟨128+3*i.val,by omega⟩

theorem coinIndex_injective : Function.Injective coinIndex := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [coinIndex] at this
  omega

theorem coin_not_pivot (i : Fin 271) : order (coinIndex i)≠1023 := by
  intro h
  have he:=congrArg Fin.val (order.injective (h.trans pivot_fixed.symm))
  have hi:=i.isLt
  simp only [coinIndex] at he
  omega

def original (coins : Fin 271 → F) : Fin 1024 → F :=
  (List.finRange 271).foldl
    (fun w i => Function.update w (order (coinIndex i)) (coins i)) (fun _ => 0)

theorem original_at (coins : Fin 271 → F) (i : Fin 271) :
    original coins (order (coinIndex i))=coins i := by
  simpa [original] using SparseGScatter.updates_at (List.finRange 271)
    (fun i => order (coinIndex i)) (order.injective.comp coinIndex_injective)
    coins (fun _ => 0) i

theorem original_pivot (coins : Fin 271 → F) : original coins 1023=0 := by
  apply SparseGScatter.updates_off
  intro i _
  exact (coin_not_pivot i).symm

theorem low_code (coins : Fin 271 → F) (j : Fin 131) :
    codeWeight (original coins) j=if j.val=128 then coins 0 else 0 := by
  unfold codeWeight
  rw [original_pivot]
  simp only [ite_self,sub_zero]
  by_cases hj : j.val=128
  · have he : lowIndex j=coinIndex 0 := by
      apply Fin.ext; simpa [lowIndex,coinIndex] using hj
    rw [he,original_at,if_pos hj]
  · rw [if_neg hj]
    apply SparseGScatter.updates_off
    intro i _ h
    have he:=congrArg Fin.val (order.injective h)
    have hb:=j.isLt
    simp only [lowIndex,coinIndex] at he
    omega

theorem point_weight (coins : Fin 271 → F) (half a b c : F) (r : Fin 128) :
    pointWeight half a b c (original coins) r=
      coins 0*ResidualModel.chordEntry half a b c r.val 128 := by
  have he (j : Fin 131) : j.val=128 ↔ j=128 := by
    constructor
    · exact fun h => Fin.ext h
    · intro h; subst j; rfl
  simp [pointWeight,low_code,he,ite_mul]

theorem source_g_boundary (half a b c : F) (previous : Fin 271 → F) (r : Fin 128) :
    pointWeight half a b c (original (SourceGConstant.finishCoins half previous)) r=
      half^10*ResidualModel.chordEntry half a b c r.val 128 := by
  rw [point_weight,SourceGConstant.coin_zero]

theorem source_code (points : Fin 3 → Fin 10 → F) (kappa : F)
    (g : Fin 1024 → F) (structured : Bool) (j : Fin 131) :
    codeWeight (sourceOriginalWeight points kappa inactive g structured) j=
      kappa*(if structured then codeWeight g j else
        codeWeight (fun r => sourcePointBasis (points 0) r.val) j)+
      kappa^2*codeWeight (fun r => sourcePointBasis (points 1) r.val) j+
      kappa^3*codeWeight (fun r => sourcePointBasis (points 2) r.val) j := by
  have hp:=pivot_inactive
  have hj : order (lowIndex j)∈inactive ↔ isInactive (order (lowIndex j))=true := by
    simp [T163SourceTable.inactive]
  cases structured <;> simp only [codeWeight,sourceOriginalWeight_eq,Bool.false_eq_true,
    Bool.true_eq,if_true,if_false,hp,hj]
  all_goals split_ifs <;> ring

theorem source_point_weight (points : Fin 3 → Fin 10 → F) (kappa half a b c : F)
    (g : Fin 1024 → F) (structured : Bool) (r : Fin 128) :
    pointWeight half a b c (sourceOriginalWeight points kappa inactive g structured) r=
      kappa*(if structured then pointWeight half a b c g r else
        pointWeight half a b c (fun i => sourcePointBasis (points 0) i.val) r)+
      kappa^2*pointWeight half a b c (fun i => sourcePointBasis (points 1) i.val) r+
      kappa^3*pointWeight half a b c (fun i => sourcePointBasis (points 2) i.val) r := by
  simp only [pointWeight,source_code,add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum]
  cases structured <;> rfl

#print axioms coinIndex_injective
#print axioms coin_not_pivot
#print axioms original_at
#print axioms original_pivot
#print axioms low_code
#print axioms point_weight
#print axioms source_g_boundary
#print axioms source_code
#print axioms source_point_weight
end
end AspisR19.TwoSwapSourceG
