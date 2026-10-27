from step import check,append
m='R1Z/PV_OptB_BoundComposition';ns='R1Z.PV_OptB_BoundComposition'
check(m)
append(m,ns,'compose_existing_charges','''/-- Exact additive accounting of the old headline. The hypotheses concern
joint failure-aware experiments; they are not claimed for the native body. -/
theorem compose_existing_charges {R M I : Type} [Fintype R] [Fintype M] [Fintype I]
    (real : R → ℚ) (middle : M → ℚ) (ideal : I → ℚ)
    (model fresh scan seed fuel : ℚ)
    (runtime_bound : |mean real - mean middle| ≤ fresh + 8 * scan + seed + fuel)
    (model_bound : |mean middle - mean ideal| ≤ model + 8 * scan + seed + fuel) :
    |mean real - mean ideal| ≤ model + fresh + 16 * scan + 2 * seed + 2 * fuel := by
  have total := compose real middle ideal _ _ runtime_bound model_bound
  linarith
''')
