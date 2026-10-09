# Fixed target-set pair mass

Source parent: `d0e3196848b89de8ddf1a85fcc0a6e55bf8fdc95`.
Status: **checked**. `RootSetPairMass` v2 passed its focused NUC check with
seven standard-only axiom audits.

The target set `S` is a finite set of admissible QM31 parameters fixed before
both draws. Its off-diagonal contains **ordered distinct pairs** and has
cardinality `m(m−1)`, where `m = S.card`. Summing the checked constant pair
mass from `NestedCircleMass` therefore gives exactly

    m(m−1) w²(1+w+w²).

The proof derives the total-success inequality instead of assuming it. For
ordinary success mass `0 ≤ σ ≤ 1`, put `k=P⁴`, `a=P²`, `u=σ/k`, `r=a*u`,
`w=u(1+r+r²)` and `N=k−a`. Then

    Nw = (σ−r)(1+r+r²) ≤ (1−r)(1+r+r²) = 1−r³ ≤ 1.

Together with `w≥0` and the checked `RetryMassArithmetic` result, this gives

    targetMass(S) ≤ m(m−1)/(N(N−1)).

For the intended later root-set instantiation, `m≤114687` and
`N=P⁴−P²=21267647892944572732387174255555510272`.  The resulting exact
endpoint is

    66429259 /
    2284408317668028910234756318256429327990468779241285843698658142054252544

or approximately `2^-214.3853278887`.  This is a conditional arithmetic
screen for the OOD-root-pair event only.  It cannot enter the global ledger
until the source-routing, point/parameter, root-cardinality, and fresh-oracle
premises described below are connected.

The zero- and one-element target sets are handled explicitly. The selected
large prime enters only through symbolic power identities and `P≥2`; neither
the field nor the raw coin space is enumerated. The actual one-call ordinary
decoder's success mass is separately shown to lie in `[0,1]`, so its final
specialization retains only the explicit history-uniform ordinary-law
premise, not another caller-supplied total-success premise.

This is a finite-kernel set sum, not a new root-count theorem. A later caller
may instantiate `S` with the admissible roots of a nonzero polynomial fixed
before both OOD samples. Establishing that the literal chronological source
sampler realizes this kernel, and establishing conditional fresh hash coins,
remain separate. No sampled-point conditioning, independent-label inference,
component extraction, or global error bound is claimed.

## Focused evidence

Both attempts ran only this new leaf on the inherited pinned NUC overlay,
via Tailscale `100.108.41.90`. Preflight found 46,616,264,704 bytes available
and no active compiler scope. Lean 4.32.0 used `-j1 -M9500`, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPU 200%, recursion depth 200 and 250,000
heartbeats. The source parent above is distinct from inherited research pin
`289d7356…` and reused V7 pin `26a9cd47…`.

- `root-set-pair-mass-nuc-v1`: exit 1, 3.39s, peak RSS 6,822,860 KiB, zero
  swaps. A redundant tactic followed an already completed rational identity;
  an implicit natural-product bound inferred the wrong second factor; and a
  linter traversing a concrete coin binder reached recursion depth 200.
- `root-set-pair-mass-nuc-v2`: exit 0, 3.42s, peak RSS 6,857,952 KiB, zero
  swaps. All seven audits use only `propext`, `Classical.choice` and
  `Quot.sound`; there were no warnings. Both provenance checks passed all
  881 entries with no change.

The repair removed the redundant tactic, supplied the explicit natural
bound, and proved the success-mass bounds generically before specializing
to the actual decoder. No linter was disabled and no resource or recursion
limit was raised. Both exact attempt snapshots, logs and manifests are
retained under `experiments/`, together with the green output.

Source/snapshot SHA-256:
`ef29448ea6d80d02fda0a6fef662b9e28ce2962454a9063088cbf7ca8b0c30f1`.
Output:
`857c7c6ab7ad22898aff5df5baa6297089cf353e2fbc0a5f14e609b5ff759cdc`.
Manifest:
`cf110ad6f04521aeb202dba363328819109d658babeb28adf2db97815367976b`.
