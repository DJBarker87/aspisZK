import RPv_FJn_LaneModel
set_option autoImplicit false
namespace AspisR1.FJn_LaneTransport
abbrev E:=AspisWideTower.WideExact
attribute [local irreducible] R0P.SemSource.laneAt
/-- Replace only proved operand identities, without exposing any lane body. -/
theorem value (p : R0P.Public E) (lambda chi theta : E)
    (o o' : R0P.Openings E) (h h' : E) (s s' : R0P.Sel E)
    (ho : o=o') (hh : h=h') (hs : s=s') :
    (∑ i : Fin 29,theta^i.val*R0P.SemSource.laneAt p lambda chi ConcretePackBasis.basis o h s i)=
    ∑ i : Fin 29,theta^i.val*R0P.SemSource.laneAt p lambda chi ConcretePackBasis.basis o' h' s' i := by
  rw [ho,hh,hs]
#print axioms value
end AspisR1.FJn_LaneTransport
