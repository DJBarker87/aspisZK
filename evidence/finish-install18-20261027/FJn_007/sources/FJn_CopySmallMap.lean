import FJn_FoldMap
set_option autoImplicit false
namespace AspisR1.FJn_CopySmallMap
variable {K L : Type} [Field K] [Field L]
/-- Naturality of the iterative powers, without concrete lambda evaluation. -/
theorem powers (f : K →+* L) (lambda : K) (i : Fin 16) :
    f (R0P.copyPowers lambda i)=R0P.copyPowers (f lambda) i := by
  unfold R0P.copyPowers
  exact FJn_FoldMap.value f _ _ _ (fun a _=>map_mul f a lambda) lambda
/-- The fixed link's branch depends only on public Nat and variant data. -/
theorem weight (f : K →+* L) (l : R0P.CopyLink) (n : Nat) (v : R0P.Variant) :
    f (R0P.copyLinkWeight l n v)=R0P.copyLinkWeight l n v := by
  unfold R0P.copyLinkWeight
  split <;> simp only [map_one,map_zero,map_natCast,map_ite]
#print axioms powers
#print axioms weight
end AspisR1.FJn_CopySmallMap
