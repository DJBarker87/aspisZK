import R1Z.PV_RunJoin_FixtureArguments
import R1Z.PV_RunJoin_FixtureRecords

/-! Identify the fixture inverse through a small product identity. Do not
normalize a concrete inverse algorithm or a hash recurrence. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureInverse
open Aeneas Aeneas.Std R0Z.WriterRefine PV_RunJoin_FixtureRecords

theorem inverse : liftU (K := M)
    PV_RunJoin_FixtureArguments.witness.pair.pair_leaf.second_occupancy_inverse =
      (digest 900 7)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  change (541081664 : M) * 1020 = 1
  rfl

#print axioms inverse
end R1Z.PV_RunJoin_FixtureInverse
