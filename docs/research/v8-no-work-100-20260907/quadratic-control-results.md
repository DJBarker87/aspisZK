# Exact quadratic-specialization control

Research parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
This is a falsification gate for the multiplicity argument in
`quadratic-specialization-review.md`, not a security experiment or a universal
specialization theorem.

## Executed scope

`experiments/quadratic_specialization_control.rs` exhausts all 25 monic
quadratics V and all 625 polynomials W of degree at most three over F5, for
R(X,Z)=V(X)^2+Z*W(X). It constructs the symbolic Sylvester determinant by
fraction-free elimination, then independently compares its five evaluations
with numeric Gaussian determinants. At square specializations it checks the
explicit kernel vectors and their independence by exact finite enumeration.
The script's matrix slot convention and Mathlib's `sylvesterMap` convention
must be mapped explicitly: Mathlib uses `(p,q) -> R*q + R'*p`.

Results from the retained v2 log:

- 15,625 restricted families; 15,000 nonzero-resultant families.
- 78,125 independent numeric determinant checks.
- 17,000 square specializations in the nonzero-resultant families.
- Maximum three square parameters in one such family.
- Root multiplicity mass 40,300; the tested multiplicity/cardinality
  inequalities all pass.
- Content, degree-drop and identically-zero-resultant guards pass their
  separate controls. The 625 zero-resultant families are not discarded
  from the experiment or counted as bounded by a nonzero root theorem.

This is exhaustive only for that polynomial family. It is not exhaustive
over bivariate polynomials, adaptive verifier strategies, or QM31.

## Evidence and resources

Source SHA256:
`0ca3312f6bbf472418328395fb2bf1b64cccd9f82e8a7aaaae1d3c7732197740`.
Runner: `experiments/run_quadratic_control_nuc.sh`.
Scope: `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`.
Command: `bash run_quadratic_control_nuc.sh <scope> quadratic-control-nuc-v2`.

The v1 attempt exited 127 before compilation because the nonlogin SSH PATH
did not contain rustc. The v2 runner uses the absolute installed rustc path;
the arithmetic source did not change. Both attempt logs and source snapshots
are retained. Rust was 1.94.1, optimized with `-O`, in a separate scope with
MemoryHigh=1 GiB, MemoryMax=2 GiB and MemorySwapMax=0.

| Stage | Exit | Wall time | Peak RSS | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Compile v2 | 0 | 0.49 s | 142,656 KiB | 0 |
| Execute v2 | 0 | 0.41 s | 1,936 KiB | 0 |

These are host-control costs, not prover time, extractor time or SBF CU.
No proof messages changed; the maximum body remains 40,282 bytes.

## What the control justifies next

The proposed sharper count depends on multiplicity, not merely on a zero
resultant. A square specialization of degree 2m supplies m independent
Sylvester kernel vectors. A symbolic proof must extend those vectors to an
invertible constant basis and derive root multiplicity at least m for the
nonzero resultant. It must also justify polynomial content normalization,
specialization degree guards, nonzero resultant and the source-shaped
candidate implication.

Until those steps are composed, the proposed `10*degZ(F)` bound is **not a
ledger entry**. Factors of Y-degree at least three, accepted uncovered
branches, efficient payment extraction, source refinement, Fiat–Shamir and
full-view hiding remain separate obligations.

## Transport continuation

Following the user's network instruction, all subsequent NUC connections use
Tailscale IP `100.108.41.90`, user `dombarker`, with strict host-key checking.
`HostKeyAlias=nuc.local` reuses the previously pinned key only; it does not
route traffic through local DNS. No existing concurrent V7 job was stopped.
