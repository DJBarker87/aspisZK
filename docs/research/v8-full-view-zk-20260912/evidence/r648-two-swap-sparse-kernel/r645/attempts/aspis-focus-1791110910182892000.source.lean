import AspisV8R19.R514DegenerateGCore
import AspisV8R19.TwoSwapSourceG

/-! Re-routes the existing 13 high directions through the TwoSwap sparse coin
locations. This is field/table algebra only; no residual coverage or source
execution claim is made. -/
set_option autoImplicit false
namespace AspisR19.R645TwoSwapHighDirections

open AspisV8R16
open AspisR19.SourceMaskTransport
open AspisR19.TwoSwapSourceTable
open AspisR19.TwoSwapSourceG
open AspisV8R17.HighRepairInvariant

noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def actualMask (half a b c : F) (q : HighRepairInvariant.Index 32 → F) : Fin 1024 → F :=
  inverseTransport inactive 1023 order (SourceMaskTransport.code half a b c q)

def actualCoin (m : Fin 1024 → F) (i : Fin 271) : F :=
  m (TwoSwapSourceTable.order (TwoSwapSourceG.coinIndex i))

theorem actual_mask_coin (half a b c : F) (q : HighRepairInvariant.Index 32 → F) (i : Fin 271) :
    actualCoin (actualMask half a b c q) i =
      SourceMaskTransport.code half a b c q (TwoSwapSourceG.coinIndex i) := by
  simp only [actualCoin, actualMask, inverseTransport,
    if_neg (TwoSwapSourceG.coin_not_pivot i), Equiv.symm_apply_apply]

theorem actual_mask_transport (half a b c : F) (q : HighRepairInvariant.Index 32 → F) :
    transport inactive 1023 order (actualMask half a b c q) =
      SourceMaskTransport.code half a b c q :=
  transport_inverse inactive 1023 pivot_inactive order _

theorem actual_mask_balanced (half a b c : F) (q : HighRepairInvariant.Index 32 → F) :
    ∑ r ∈ inactive, actualMask half a b c q r = 0 := by
  have h := congrFun (actual_mask_transport half a b c q) (1023 : Fin 1024)
  simp only [transport, pivot_fixed, ↓reduceIte] at h
  exact h.trans (SourceMaskTransport.code_pivot_zero half a b c q)

theorem actual_selected_coins_zero (t : Fin 22 → F)
    (half alpha a b c : F) (j : Fin 13) (i : Fin 271) :
    actualCoin (actualMask half a b c
      (SourceCircleBoundary.column t alpha j)) i = 0 := by
  rw [actual_mask_coin]
  exact R514DegenerateGCore.source_selected_g_zero t half alpha a b c j i

#print axioms actual_mask_coin
#print axioms actual_mask_transport
#print axioms actual_mask_balanced
#print axioms actual_selected_coins_zero

end
end AspisR19.R645TwoSwapHighDirections
