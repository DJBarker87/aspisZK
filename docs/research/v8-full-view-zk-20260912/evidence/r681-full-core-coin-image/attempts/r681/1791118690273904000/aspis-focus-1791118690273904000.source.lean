import AspisV8R19.R680CoreQuotientSupport
import AspisV8R19.R662FullIndexedMaskPreservation
set_option autoImplicit false
namespace AspisV8R19.R681FullCoreCoinImage
open AspisR19 AspisV8R17 HighRepairInvariant
open R574SparseGCorePolynomial R680CoreQuotientSupport
open R645TwoSwapHighDirections R661TwoSwapMaskAddition R662FullIndexedMaskPreservation
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]
def coreQuotient (alpha : F) (x : Fin 271 → F) (i : Index 256) : F :=
  weightedQ alpha x (4*i.1.val+i.2.val)
theorem core_flatten (alpha : F) (x : Fin 271 → F) :
    flattenFull (coreQuotient alpha x) = weightedQ alpha x := by
  funext r
  by_cases hr : r < 1024
  · simp only [flattenFull,dif_pos hr,coreQuotient,Nat.div_add_mod]
  · simp only [flattenFull,dif_neg hr]
    exact (weightedQ_support alpha x r (by omega)).symm

theorem core_firstFold (alpha : F) (x : Fin 271 → F) (d : Fin 256) :
    R370KernelEvaluation.firstFold 256 alpha (coreQuotient alpha x) d = 0 := by
  simp only [R370KernelEvaluation.firstFold,coreQuotient,Fin.sum_univ_succ]
  have h0 : (4*d.val)/4=d.val := by omega
  have h1 : (4*d.val+1)/4=d.val := by omega
  have h2 : (4*d.val+2)/4=d.val := by omega
  have h3 : (4*d.val+3)/4=d.val := by omega
  have hm0 : (4*d.val)%4=0 := by omega
  have hm1 : (4*d.val+1)%4=1 := by omega
  have hm2 : (4*d.val+2)%4=2 := by omega
  have hm3 : (4*d.val+3)%4=3 := by omega
  simp only [weightedQ,nz,ch,Fin.val_zero,Fin.val_succ,add_zero,h0,h1,h2,h3,hm0,hm1,hm2,hm3]
  norm_num only
  ring

theorem core_coin (half alpha a b c : F) (x : Fin 271 → F) (i : Fin 271) :
    actualCoin (indexedMask half a b c (coreQuotient alpha x)) i =
      coreMap half alpha a b c x i := by
  simp only [actualCoin,indexedMask,fullMask,SourceMaskTransport.inverseTransport,
    if_neg (TwoSwapSourceG.coin_not_pivot i),Equiv.symm_apply_apply]
  rw [core_flatten]
  rfl

theorem core_balance (half alpha a b c : F) (x : Fin 271 → F) :
    (∑ r ∈ TwoSwapSourceTable.inactive,
      indexedMask half a b c (coreQuotient alpha x) r) = 0 := by
  have h := congrFun (SourceMaskTransport.transport_inverse TwoSwapSourceTable.inactive
    1023 TwoSwapSourceTable.pivot_inactive TwoSwapSourceTable.order
    (fun j => sourceChord half (weightedQ alpha x) a b c j.val)) (1023:Fin 1024)
  change SourceMaskTransport.transport TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (SourceMaskTransport.inverseTransport TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
      (fun j => sourceChord half (weightedQ alpha x) a b c j.val)) 1023 = _ at h
  simp only [SourceMaskTransport.transport,TwoSwapSourceTable.pivot_fixed,↓reduceIte] at h
  unfold indexedMask fullMask
  rw [core_flatten]
  exact h.trans (HighQueryGCore.sourceChord_support half (weightedQ alpha x) 470
    (weightedQ_support alpha x) a b c 1023 (by omega))

/-- All 271 core targets can be attained in the full source-shaped field model.
Query normalization, point/relation repair, actual legal witness targets and
causal commitments remain separate obligations. -/
theorem full_core_coin_image (half alpha a b c : F) (target : Fin 271 → F)
    (hdet : (coreMatrix half alpha a b c).det ≠ 0) :
    ∃ x : Fin 271 → F,
      (∀ i, actualCoin (indexedMask half a b c (coreQuotient alpha x)) i = target i) ∧
      (∀ d, R370KernelEvaluation.firstFold 256 alpha (coreQuotient alpha x) d = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive,
        indexedMask half a b c (coreQuotient alpha x) r) = 0 := by
  have hs : Function.Surjective (coreMatrix half alpha a b c).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  obtain ⟨x,hx⟩ := hs target
  refine ⟨x,?_,core_firstFold alpha x,core_balance half alpha a b c x⟩
  intro i
  rw [core_coin,← coreMatrix_mulVec]
  exact congrFun hx i
#print axioms core_flatten
#print axioms core_firstFold
#print axioms core_coin
#print axioms core_balance
#print axioms full_core_coin_image
end
end AspisV8R19.R681FullCoreCoinImage
