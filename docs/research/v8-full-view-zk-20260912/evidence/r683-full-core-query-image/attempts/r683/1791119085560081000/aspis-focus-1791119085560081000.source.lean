import AspisV8R19.R681FullCoreCoinImage
import AspisV8R19.R682FullQueryNormalization
set_option autoImplicit false
namespace AspisV8R19.R683QueryCoreCoinImage
open AspisR19 AspisV8R16 AspisV8R17 HighRepairInvariant
open R574SparseGCorePolynomial R680CoreQuotientSupport R681FullCoreCoinImage
open R682FullQueryNormalization R645TwoSwapHighDirections
open R661TwoSwapMaskAddition R662FullIndexedMaskPreservation
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]
theorem flatten_same_high (q v : Index 256 → F)
    (same : ∀ i : Index 256, 22 ≤ i.1.val → q i = v i) (r : Nat) (hr : 88 ≤ r) :
    flattenFull q r = flattenFull v r := by
  unfold flattenFull
  split_ifs with h
  · exact same _ (by change 22 ≤ r/4; omega)
  · rfl

theorem core_high_coin (half alpha a b c : F) (x : Fin 271 → F)
    (v : Index 256 → F)
    (same : ∀ i : Index 256, 22 ≤ i.1.val → v i = coreQuotient alpha x i)
    (i : Fin 271) :
    actualCoin (indexedMask half a b c v) i = coreMap half alpha a b c x i := by
  simp only [actualCoin,indexedMask,fullMask,R562.inverseChordMessage,inverseTransport,
    if_neg (TwoSwapSourceG.coin_not_pivot i),Equiv.symm_apply_apply]
  have h := HighQueryGCore.low_repair_preserves_g half (flattenFull v)
    (flattenFull (coreQuotient alpha x)) (flatten_same_high v _ same) a b c i
  rw [h,core_flatten]
  rfl

theorem core_high_balance (half alpha a b c : F) (x : Fin 271 → F)
    (v : Index 256 → F)
    (same : ∀ i : Index 256, 22 ≤ i.1.val → v i = coreQuotient alpha x i) :
    (∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c v r) = 0 := by
  have hs : ∀ r, 940 ≤ r → flattenFull v r = 0 := by
    intro r hr
    rw [flatten_same_high v _ same r (by omega),core_flatten]
    exact weightedQ_support alpha x r hr
  have h := congrFun (transport_inverse TwoSwapSourceTable.inactive 1023
    TwoSwapSourceTable.pivot_inactive TwoSwapSourceTable.order
    (fun j => sourceChord half (flattenFull v) a b c j.val)) (1023:Fin 1024)
  simp only [transport,TwoSwapSourceTable.pivot_fixed,↓reduceIte] at h
  exact h.trans (HighQueryGCore.sourceChord_support half (flattenFull v) 470 hs
    a b c 1023 (by omega))

/-- Conditional full-dimensional core image with all modeled query and first-fold
constraints retained. This is a field construction after fixing challenges;
it is not a causal simulator or a universal legal-witness compatibility proof. -/
theorem query_core_coin_image (half alpha a b c : F) (target : Fin 271 → F)
    (t : Fin 22 → F) (ht : Function.Injective t)
    (hdet : (coreMatrix half alpha a b c).det ≠ 0) :
    ∃ v : Index 256 → F,
      (∀ i, actualCoin (indexedMask half a b c v) i = target i) ∧
      (∀ slot : Fin 4, ∀ root : Fin 22,
        evaluate256 (fun d => v (d,slot)) (t root) = 0) ∧
      (∀ d, R370KernelEvaluation.firstFold 256 alpha v d = 0) ∧
      (∑ r ∈ TwoSwapSourceTable.inactive, indexedMask half a b c v r) = 0 := by
  obtain ⟨x,hcoins,hfold,hbalance⟩ := full_core_coin_image half alpha a b c target hdet
  obtain ⟨v,hquery,hfv,hsame⟩ := full_query_normalization (coreQuotient alpha x) alpha t ht hfold
  refine ⟨v,?_,hquery,hfv,core_high_balance half alpha a b c x v hsame⟩
  intro i
  rw [core_high_coin half alpha a b c x v hsame,← core_coin]
  exact hcoins i
#print axioms flatten_same_high
#print axioms core_high_coin
#print axioms core_high_balance
#print axioms query_core_coin_image
end
end AspisV8R19.R683QueryCoreCoinImage
