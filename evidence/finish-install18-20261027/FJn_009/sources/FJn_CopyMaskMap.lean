import FJn_FoldMap
set_option autoImplicit false
namespace AspisR1.FJn_CopyMaskMap
variable {K L : Type} [Field K] [Field L]
def selectors (f : K →+* L) (s : R0P.CopySelectors K) : R0P.CopySelectors L :=
  ⟨fun i=>f (s.high i),fun i=>f (s.low i)⟩
theorem mask (f : K →+* L) (low : Fin 16 → K) (m : Nat) :
    f (R0P.copySelectorMaskSum16 low m)=R0P.copySelectorMaskSum16 (fun i=>f (low i)) m := by
  unfold R0P.copySelectorMaskSum16
  dsimp only
  rw [FJn_FoldMap.value f _ _ _ (by intro a i;split <;> simp only [map_sub,map_add])]
  split <;> simp only [map_one,map_zero]
attribute [local irreducible] R0P.copyActiveRowMasks R0P.copySelectorMaskSum16
theorem active (f : K →+* L) (s : R0P.CopySelectors K) :
    f (R0P.copyActiveLiteral s)=R0P.copyActiveLiteral (selectors f s) := by
  unfold R0P.copyActiveLiteral
  rw [FJn_FoldMap.value f _ _ _ (by
    intro a i
    split <;> simp only [map_add,map_mul,mask,selectors])]
  rw [map_zero]
#print axioms mask
#print axioms active
end AspisR1.FJn_CopyMaskMap
