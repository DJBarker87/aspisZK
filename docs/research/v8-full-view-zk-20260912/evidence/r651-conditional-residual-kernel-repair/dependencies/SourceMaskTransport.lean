import AspisV8R19.T163SourceTable
import AspisV8R19.NormalizedGCore
import AspisV8R17.LegalMaskCoordinates

/-! The source-pinned T163 inverse sends each low quotient chord to a
legal balanced G-table correction. Active coordinates are allowed to change:
this is NOT the H1 padding-mask restriction. No seed or oracle law is used. -/
namespace AspisR19.SourceMaskTransport
open AspisV8R16 AspisV8R17 HighRepairInvariant NormalizedGCore T163SourceTable
noncomputable section
variable {F : Type*} [CommRing F]

def code (half a b c : F) (q : Index 32 → F) (r : Fin 1024) : F :=
  sourceChord half (flatten q) a b c r.val
def mask (half a b c : F) (q : Index 32 → F) : Fin 1024 → F :=
  inverseTransport inactive 1023 order (code half a b c q)
def coinIndex (i : Fin 271) : Fin 1024 := ⟨128+3*i.val,by omega⟩
def mixedCoin (m : Fin 1024 → F) (i : Fin 271) : F := m (order (coinIndex i))

theorem code_tail (half a b c : F) (q : Index 32 → F) (r : Fin 1024)
    (hr : 131 ≤ r.val) : code half a b c q r=0 := by
  apply HighQueryGCore.sourceChord_support half _ 64 _ a b c _ (by omega)
  intro i hi
  simp [flatten,show ¬i<128 by omega]

theorem code_pivot_zero (half a b c : F) (q : Index 32 → F) :
    code half a b c q 1023=0 := code_tail half a b c q 1023 (by decide)

theorem inverse_pivot_fixed : order.symm (1023 : Fin 1024)=1023 := by
  have h := congrArg order.symm pivot_fixed
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem mask_transport (half a b c : F) (q : Index 32 → F) :
    transport inactive 1023 order (mask half a b c q)=code half a b c q :=
  transport_inverse inactive 1023 pivot_inactive order _

theorem mask_balanced (half a b c : F) (q : Index 32 → F) :
    ∑ r ∈ inactive, mask half a b c q r=0 := by
  have h := congrFun (mask_transport half a b c q) (order.symm 1023)
  simp only [transport,Equiv.apply_symm_apply,↓reduceIte] at h
  rw [inverse_pivot_fixed,code_pivot_zero] at h
  exact h

theorem mask_is_legal_free_lift (half a b c : F) (q : Index 32 → F) :
    (legalMaskEquiv inactive 1023 pivot_inactive
      (fun i => mask half a b c q i.val)).val=mask half a b c q := by
  have h := (legalMaskEquiv (F:=F) inactive 1023 pivot_inactive).right_inv
    ⟨mask half a b c q,mask_balanced half a b c q⟩
  exact congrArg Subtype.val h

theorem mask_preserves_balance (half a b c : F) (q : Index 32 → F)
    (g : Fin 1024 → F) (hg : ∑ r ∈ inactive, g r=0) :
    ∑ r ∈ inactive, (g r+mask half a b c q r)=0 := by
  rw [Finset.sum_add_distrib,hg,mask_balanced,add_zero]

theorem coin_not_pivot (i : Fin 271) : order (coinIndex i) ≠ 1023 := by
  intro h
  have he := order.injective (h.trans pivot_fixed.symm)
  have hi := congrArg Fin.val he
  have hn := i.isLt
  simp only [coinIndex,Fin.val_ofNat] at hi
  omega

theorem mask_coin (half a b c : F) (q : Index 32 → F) (i : Fin 271) :
    mixedCoin (mask half a b c q) i=code half a b c q (coinIndex i) := by
  simp only [mixedCoin,mask,inverseTransport,if_neg (coin_not_pivot i),
    Equiv.symm_apply_apply]

section Field
variable {K : Type*} [Field K] [NeZero (2 : K)]

theorem normalized_mask_coins_zero (t : Fin 22 → K) (ht : Function.Injective t)
    (half alpha a b c : K) (j : Fin 13) (i : Fin 271) :
    mixedCoin (mask half a b c
      (NormalizedQuotient.quotient t ht alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j))) i=0 := by
  rw [mask_coin]
  exact normalized_selected_g_zero t ht half alpha a b c j i

theorem normalized_mask_boundary (t : Fin 22 → K) (ht : Function.Injective t)
    (half alpha a b c : K) (j : Fin 13) :
    let q := NormalizedQuotient.quotient t ht alpha
      (SparseHighWitness.degree j) (SparseHighWitness.slot j)
    transport inactive 1023 order (mask half a b c q)=code half a b c q ∧
    (∑ r ∈ inactive, mask half a b c q r)=0 ∧
    (∀ i, mixedCoin (mask half a b c q) i=0) :=
  ⟨mask_transport half a b c _,mask_balanced half a b c _,
    normalized_mask_coins_zero t ht half alpha a b c j⟩
end Field

#print axioms code_tail
#print axioms code_pivot_zero
#print axioms inverse_pivot_fixed
#print axioms mask_transport
#print axioms mask_balanced
#print axioms mask_is_legal_free_lift
#print axioms mask_preserves_balance
#print axioms coin_not_pivot
#print axioms mask_coin
#print axioms normalized_mask_coins_zero
#print axioms normalized_mask_boundary
end
end AspisR19.SourceMaskTransport
