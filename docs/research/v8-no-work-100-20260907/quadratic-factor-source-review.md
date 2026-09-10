# Actual factor root to quadratic parity input

Status: green on the first focused NUC check, with six standard-only axiom
audits. The exact source, output and attempt evidence are frozen.

Source drafted at `9bc0ceee408f432c879ff2239e3ec565dedcd409`; the preceding
12-leaf checkpoint was committed as `2c63df5aab97b826d652b2536fa269bc250386d3`
while this leaf was checked. This leaf was not part of that checkpoint.
The existing NUC
scope was created at `289d7356c78a4cd493fe61a54f9548f2a0c11298`; reused V7
source is pinned to `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

[QuadraticFactorSource.lean](experiments/QuadraticFactorSource.lean) connects
the actual maintained factor homomorphisms to `QuadraticConstructedParity.RootsAt`.
The V7 factor representation is `K[X][Z][Y]`: Y is outermost, Z is the
middle batching challenge, and X is the innermost evaluation variable.
`specializeChallenge gamma` maps `eval(C gamma)` over Y coefficients;
`challengeCandidateHom gamma U` then evaluates Y at U(X).

The parity consumer uses coefficients in `K[Z][X]`. Its three coefficients
are constructed, not supplied:

```
a = swap(F.coeff 2)
b = swap(F.coeff 1)
c = swap(F.coeff 0)
D = b^2 - 4*a*c
```

The symbolic three-term expansion for `deg_Y F <= 2` is proved over the
coefficient ring. Existing `FactorIdentityCover.coeff_swap_eval` gives the
exact coefficient identity `P.eval(C gamma) = map(eval gamma)(swap P)`.
Together these yield the literal value of `challengeCandidateHom gamma U F`
as `a_gamma*U^2 + b_gamma*U + c_gamma`. Hence an actual zero and degree Y
equal to two supply `RootsAt a b c gamma` with the *same* U. There is no
assumed correspondence, expected trace, candidate curve, or verifier success.
U may have been selected after gamma and alpha.

The degree companion uses the pinned V7
`coeff_weight_le_localBivariateWeight`. It handles an identically zero
coefficient separately, so no nonzero support premise is smuggled in.
Every coefficient's Z degree is at most `trivariateYZWeight curveDegree F`.
Swap involution and the polynomial sum/product degree inequalities then
give `deg_Z D <= 2*trivariateYZWeight curveDegree F`. This includes the
actual full batching weight 28; it does not replace that challenge by the
degree-two helper curve.

Verified audits: `quadratic_shape`, `coefficient_specialization`,
`candidate_value`, `candidate_root`, `coefficient_degree_le_weight`, and
`discriminant_degree_le_weight`. All depend only on `propext`,
`Classical.choice` and `Quot.sound`; no `sorry` or new axiom is retained.

Inspected V7 sources match the borrowed commit exactly (read-only git diff):
Factors SHA-256 `112e16cd05454f76e65958025ed01fd45e07dd2cf0632ee5eb53e2170b4ad8f3`;
FactorBudgets SHA-256 `ced62421bc10c37b03bbe780b0c7b94183ced4ddb1f42128aeb12637acab7866`.
The green `FactorIdentityCover` and `QuadraticConstructedParity` outputs
are reused; no cold dependency build or modification to their source is
authorized by this leaf.

The v1 run exited 0 in 3.39s, peak RSS 6844804 KiB, zero swaps. Exact local
artifacts are `experiments/quadratic-factor-source-nuc-v1-source.txt`,
`experiments/quadratic-factor-source-nuc-v1.log`,
`experiments/quadratic-factor-source-nuc-v1-manifest.json` and
`experiments/QuadraticFactorSource.olean`. There was no failed or repeated
attempt for this leaf.

Source and snapshot SHA-256:
`20b0dcf88c3ddbc230459c221fbd6f92dc8ddadb24b53780f7913358743efd9b`.
Olean SHA-256:
`fc21f4c8b807c18fc221f52446973a6cc701ecf51097ef834e40047766c679db`.
Log SHA-256:
`3133f56b451cddba16d254818f3a60c5c76942c2f031c93acd10ea3a8f9c816c`.
Manifest SHA-256:
`1bbb829bbb88e8e74d552152dd00c8ae9879d61a919c16630fc527c000c5d3da`.

Historical command, not an unchanged replay instruction:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes \
  -o HostKeyAlias=nuc.local dombarker@100.108.41.90 \
  'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  QuadraticFactorSource quadratic-factor-source-nuc-v1'
```

The prelaunch read-only reservation check found no running user build scope
and 43 GiB available. The job used Lean 4.32.0, `-j1 -M9500`, MemoryHigh 8GiB,
MemoryMax 10GiB, MemorySwapMax 0 and CPUQuota 200%. All 833 overlay artifacts
passed the before/after provenance checks unchanged. Native package builds
remain a pinned-revision cache boundary. Tailscale carried the connection;
`nuc.local` was only the verified host-key alias. The sole compiler slot was
released after terminal postflight. No concurrent V7 state was changed.

Irreducibility, discriminant nonzeroness, characteristic degree limits,
constant-X parity, pre-challenge factor selection, and acceptance-to-same-factor
root coverage remain separate composition obligations. This is a source-model
algebra bridge, not a Rust-machine translation, full security theorem,
or efficient payment extractor. No production/default, proof-size, CU,
transcript or grinding change is made.
