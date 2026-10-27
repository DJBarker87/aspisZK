import RPt_FJo_CircleModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_QueryLaw
open AspisWide.FinalEncoder
abbrev E := AspisWideTower.WideExact
/-- A per-index proposition only; all source values are fixed before induction. -/
def Step (data : MatchingSupport.Data E) (q : Fin 22 → Fin 262144)
    (next query : Nat) (x y : E) (j : Fin 22) : Prop :=
  next=j.val → x=(exactCircleX (q j))⁻¹ → y=(exactCircleY (q j))⁻¹ →
    query=(q j).val → MatchingSupport.match0 data (q j)
end AspisR1.FJp_QueryLaw
end
