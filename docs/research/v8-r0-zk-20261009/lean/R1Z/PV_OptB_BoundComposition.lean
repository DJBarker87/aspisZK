import R1Z.PV_OptB_JointTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_BoundComposition
open R0Z

/-- Composition is on the JOINT failure-aware tests. A bound on the old
successful marginals cannot be substituted for `model_bound`. -/
theorem compose {R M I : Type} [Fintype R] [Fintype M] [Fintype I]
    (real : R → ℚ) (middle : M → ℚ) (ideal : I → ℚ) (εr εm : ℚ)
    (runtime_bound : |mean real - mean middle| ≤ εr)
    (model_bound : |mean middle - mean ideal| ≤ εm) :
    |mean real - mean ideal| ≤ εr + εm :=
  (abs_sub_le (mean real) (mean middle) (mean ideal)).trans
    (add_le_add runtime_bound model_bound)

#print axioms compose
/-- Exact additive accounting of the old headline. The hypotheses concern
joint failure-aware experiments; they are not claimed for the native body. -/
theorem compose_existing_charges {R M I : Type} [Fintype R] [Fintype M] [Fintype I]
    (real : R → ℚ) (middle : M → ℚ) (ideal : I → ℚ)
    (model fresh scan seed fuel : ℚ)
    (runtime_bound : |mean real - mean middle| ≤ fresh + 8 * scan + seed + fuel)
    (model_bound : |mean middle - mean ideal| ≤ model + 8 * scan + seed + fuel) :
    |mean real - mean ideal| ≤ model + fresh + 16 * scan + 2 * seed + 2 * fuel := by
  have total := compose real middle ideal _ _ runtime_bound model_bound
  linarith

#print axioms compose_existing_charges
end R1Z.PV_OptB_BoundComposition
