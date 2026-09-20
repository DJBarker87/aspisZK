import AspisV8R17.TwoChannelOpening

/-! Algebra matching the staged all-minus-G split. The arguments are
arbitrary, including malformed submitted quotients. This file does not
assert that authenticated Rust bytes refine these additive maps. -/
set_option autoImplicit false
namespace AspisV8R17
variable {V F : Type*} [AddCommGroup V] [AddCommGroup F]

/-- Replacing just G's functional in a batch is a correction, not applying
the G functional to the entire combined message. In the host, `g` already
includes gamma^27 and `all - g` includes the other 28 columns. -/
theorem projected_claim (u v : V →+ F) (all g : V) :
    u (all - g) + v g = u all + (v g - u g) := by
  rw [map_sub]
  abel

/-- Pull the projected claim back through the common reversible transport.
No premise equates a supplied claim with its committed value. -/
theorem transported_projected_claim (T : V ≃+ V) (u v : V →+ F)
    (all g : V) :
    u (T.symm (all - g)) + v (T.symm g) =
      u (T.symm all) + (v (T.symm g) - u (T.symm g)) := by
  simp only [map_sub]
  abel

/-- The difference between the corrected claim and the two quotient
functionals is exactly the sum of the two extracted-column residuals.
In particular this theorem does NOT infer that either residual is zero
from a zero combined value: that needs the separate extraction/batching
argument and its bad-event bound. -/
theorem channel_residual_identity (T : V ≃+ V) (L : V →+ V)
    (u v : V →+ F) (all g iR iG qR qG : V) :
    (u (T.symm (all - g)) + v (T.symm g) -
      u (T.symm iR) - v (T.symm iG)) -
      (quotientFunctional T L u qR + quotientFunctional T L v qG) =
    u (T.symm (all - g - iR - L qR)) +
      v (T.symm (g - iG - L qG)) := by
  simp only [quotientFunctional, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, map_sub]
  abel

/-- A claimed scalar may itself be false. Its independent discrepancy
must be retained in addition to the two opening residuals. -/
theorem claimed_channel_residual_identity (T : V ≃+ V) (L : V →+ V)
    (u v : V →+ F) (all g iR iG qR qG : V) (claimed : F) :
    claimed - u (T.symm iR) - v (T.symm iG) -
      (quotientFunctional T L u qR + quotientFunctional T L v qG) =
    (claimed - (u (T.symm (all - g)) + v (T.symm g))) +
      u (T.symm (all - g - iR - L qR)) +
      v (T.symm (g - iG - L qG)) := by
  simp only [quotientFunctional, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, map_sub]
  abel

#print axioms projected_claim
#print axioms transported_projected_claim
#print axioms channel_residual_identity
#print axioms claimed_channel_residual_identity
end AspisV8R17
