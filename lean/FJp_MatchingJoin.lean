import FJp_CircleTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_MatchingJoin
variable {K : Type} [Field K]
/-- Pure equality chain, with coordinate transports checked separately. -/
theorem value (a a' x x' y y' selected target folded : K) (v v' : Fin 4 → K)
    (ha : a=a') (hx : x=x') (hy : y=y') (hv : v=v')
    (circle : selected=FoldRuntimeAlgebra.circleWithInverses a x y v)
    (model : FoldRuntimeAlgebra.circleWithInverses a' x' y' v'=folded)
    (chosen : selected=target) : folded=target := by
  have hα := FJp_CircleTransport.alpha a a' x y v ha
  have hₓ := FJp_CircleTransport.x a' x x' y v hx
  have hᵧ := FJp_CircleTransport.y a' x' y y' v hy
  have hᵥ := FJp_CircleTransport.dots a' x' y' v v' hv
  exact (circle.trans (hα.trans (hₓ.trans (hᵧ.trans (hᵥ.trans model))))).symm.trans chosen
#print axioms value
end AspisR1.FJp_MatchingJoin
end
