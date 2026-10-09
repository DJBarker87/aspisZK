import R0P.SemD3Glue

/-! Lead: the characteristic premise of `SemD3Glue.d3`, discharged.
`SemE = WideExact` is an algebra over `ZMod P` (the instance `TypedContext`
already uses); the algebra map of a field into a nontrivial ring is injective,
so the characteristic transfers. -/
set_option autoImplicit false
namespace R0P.SemD3Glue
open AspisWideTower

noncomputable section

instance semE_charP : CharP SemE AspisCircleGroupOrder.P :=
  charP_of_injective_algebraMap
    (algebraMap (ZMod AspisCircleGroupOrder.P) SemE).injective AspisCircleGroupOrder.P

theorem semE_prime_eq : AspisCircleGroupOrder.P = 2 ^ 31 - 1 := by
  norm_num [AspisCircleGroupOrder.P]

#print axioms semE_charP
#print axioms semE_prime_eq
end
end R0P.SemD3Glue
