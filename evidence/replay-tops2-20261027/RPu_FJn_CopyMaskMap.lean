import RPu_FJn_FoldMap
set_option autoImplicit false
namespace AspisR1.FJn_CopyMaskMap
variable {K L : Type} [Field K] [Field L]
def selectors (f : K →+* L) (s : R0P.CopySelectors K) : R0P.CopySelectors L :=
  ⟨fun i=>f (s.high i),fun i=>f (s.low i)⟩
theorem mask (f : K →+* L) (low : Fin 16 → K) (m : Nat) :
    f (R0P.copySelectorMaskSum16 low m)=R0P.copySelectorMaskSum16 (fun i=>f (low i)) m := by
  unfold R0P.copySelectorMaskSum16
  dsimp only
  split
  · simpa only [map_one] using FJn_FoldMap.value f _ _
      (fun sum i=>sum-f (low i)) (fun a i=>map_sub f a (low i)) (1:K)
  · simpa only [map_zero] using FJn_FoldMap.value f _ _
      (fun sum i=>sum+f (low i)) (fun a i=>map_add f a (low i)) (0:K)
attribute [local irreducible] R0P.copyActiveRowMasks R0P.copySelectorMaskSum16
theorem active (f : K →+* L) (s : R0P.CopySelectors K) :
    f (R0P.copyActiveLiteral s)=R0P.copyActiveLiteral (selectors f s) := by
  unfold R0P.copyActiveLiteral
  rw [FJn_FoldMap.value f _ _
    (fun sum i=>if R0P.copyActiveRowMasks i≠0 then sum+f (s.high i)*
      R0P.copySelectorMaskSum16 (fun j=>f (s.low j)) (R0P.copyActiveRowMasks i) else sum)
    (by intro a i;dsimp only;split <;> simp only [map_add,map_mul,mask])]
  rw [map_zero]
  rfl
#print axioms mask
#print axioms active
end AspisR1.FJn_CopyMaskMap
