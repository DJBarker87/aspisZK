# R541 joint Schur equivalence evidence

- Target: `AspisV8R19/R541JointSchurEquivalence.lean`
- Exact scratch source: `.r21-scratch/r541-joint-schur-equivalence/R541JointSchurEquivalence.lean`
- Source SHA-256: `9301d8eee802dcc2ee453f32b92a66b4817c8c6436ede3fd8e285d2c00608b71`
- Source revision: `15fff778d94ca208a5ea8cc97fb08e0a8e0f9259`
- Final exit status: `0`
- Wall time: `0:00.95`
- Peak Lean-child RSS KiB: `1763636`
- Swaps: `0`
- Cgroup: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`
- Lean flags: `-j1 -M4500`

The final log contains complete `#print axioms` output:
`joint_schur_equivalence` depends only on `[propext, Classical.choice, Quot.sound]`.

The theorem is generic linear algebra under exactly the visible hypotheses
`H u0 = h`, `range K = ker H`, and `ker D = range T`. It proves the two-way
affine-system/Schur-obstruction equivalence. It does not instantiate a source
premise, prove source image coverage, or establish privacy or security.

Attempt history is retained in `evidence/`: the first stopped because
`AspisV8Privacy.PublicCosetRepair.olean` was unavailable in the cache; the
next two are focused proof errors; the last is green. No cold dependency build
was run.
