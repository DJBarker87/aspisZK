import RPt_FJp_MatchingJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_LiteralJoin
open AspisWide.FinalEncoder
abbrev E := AspisWideTower.WideExact
attribute [local irreducible] TwoFoldExtraction.batchedWord FirstFold.fibre FirstFold.foldWord
/-- Literal matching from one query's values, with no source evaluation. -/
theorem value (data : MatchingSupport.Data E) (i : Fin 262144)
    (alpha ix iy selected : E) (dots : Fin 4 → E)
    (ha : alpha=data.alpha0) (hx : ix=(exactCircleX i)⁻¹) (hy : iy=(exactCircleY i)⁻¹)
    (hd : dots=FirstFold.fibre (TwoFoldExtraction.batchedWord data.W data.gamma) i)
    (hc : selected=FoldRuntimeAlgebra.circleWithInverses alpha ix iy dots)
    (hs : selected=data.V i) : MatchingSupport.match0 data i := by
  unfold MatchingSupport.match0
  with_reducible exact (FJp_MatchingJoin.value alpha data.alpha0 ix (exactCircleX i)⁻¹ iy (exactCircleY i)⁻¹
    selected (data.V i) (FirstFold.foldWord data.alpha0 (TwoFoldExtraction.batchedWord data.W data.gamma) i)
    dots (FirstFold.fibre (TwoFoldExtraction.batchedWord data.W data.gamma) i) ha hx hy hd hc
    (FJo_CircleInverses.value data.alpha0 (TwoFoldExtraction.batchedWord data.W data.gamma) i) hs)
#print axioms value
end AspisR1.FJp_LiteralJoin
end
