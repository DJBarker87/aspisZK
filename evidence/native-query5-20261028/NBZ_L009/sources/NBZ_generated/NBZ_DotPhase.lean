import NBZ_DotBounds
set_option autoImplicit false
namespace NBZ_DotPhase
/-- The natural-sum prestate of every actual inner base-prefix iteration
satisfies the retained integer fragment's phase envelope. -/
theorem caller (xs : List (Nat×Nat)) (size : xs.length<4)
 (canonical : ∀ x∈xs,x.1<2^31-1 ∧ x.2<2^31-1) :
 NBB_Phase.Bound xs.length (NBZ_DotBounds.sumProducts xs) := by
 have h := NBZ_DotBounds.sum_bound xs canonical
 unfold NBB_Phase.Bound
 rw [Nat.mod_eq_of_lt size]
 change NBZ_DotBounds.sumProducts xs<2^34+xs.length*NBZ_DotBounds.P2
 omega
#print axioms caller
end NBZ_DotPhase
