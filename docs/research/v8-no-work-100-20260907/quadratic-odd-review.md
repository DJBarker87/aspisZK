# Odd parity degree gives a fixed leading-coefficient exception

Working parent: `9bc0ceee408f432c879ff2239e3ec565dedcd409`; reused NUC-scope
parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`; borrowed source pin:
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

[QuadraticSpecializationOdd.lean](experiments/QuadraticSpecializationOdd.lean)
is green with five standard-only axiom audits. It proves the odd-degree
counterpart of the [guarded even-degree count](quadratic-guarded-review.md).

Fix `aF,bF,cF,H,R` in `K[Z][X]` with the literal equality
`bF^2-4*aF*cF = H^2*R`, and suppose R has odd global X degree. The exceptional
polynomial is constructed as `E(Z)=R.leadingCoeff`, not supplied as an
arbitrary bad set. Odd degree proves R and E nonzero. If every X coefficient
of R has Z degree at most delta, then `deg E <= delta` directly from the
actual leading coefficient's index.

For any gamma where `H_gamma != 0`, an actual polynomial quadratic root U
forces `E(gamma)=0`. Indeed, otherwise the polynomial-map leading-coefficient
theorem preserves R's odd degree, so R_gamma is nonzero. The discriminant
identity and checked polynomial cancellation then give `R_gamma=V^2`.
Taking degrees contradicts oddness. Neither R_gamma nonzero nor preserved
degree is assumed: both are derived in the contradiction branch.

Consequently any finite G consisting of such actual quadratic roots, with
H_gamma nonzero, has `|G| <= delta`. Each U is existential separately for
its own gamma and can be adaptive. There is no resultant assumption, even
matrix padding, characteristic-zero assumption or forward-moved candidate.
The proof counts roots of the literal fixed E.

The five audited endpoints are `leading_obstruction_nonzero`,
`leading_obstruction_degree`, `actual_root_forces_leading_zero`,
`leading_exception_card_le` and `guarded_odd_roots_card_le`. Every audit uses
only `propext`, `Classical.choice` and `Quot.sound`; no `sorry` or new axiom
is retained.

The first focused run passed: exit 0, 1.41s wall time, peak RSS 2423964 KiB,
zero swaps. Exact v1 source snapshot/log/manifest and the green olean are
retained under `experiments/quadratic-specialization-odd-nuc-v1*` and
`experiments/QuadraticSpecializationOdd.olean`.

Source SHA-256:
`248b99f37de95962302296faf649c5e645caaee2a70dace7b9f13febb5af00b7`.
Olean SHA-256:
`e66d4b3095466e8866877877ea6ac660f51ca2ccb15eabf6b0bee02fddd9732e`.
Manifest SHA-256:
`0948e6c5481467734b49d959d4caeb75e01df44951a9faf49faa2db56fb3ae06`.

Historical command, not an unchanged replay instruction:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes \
  -o HostKeyAlias=nuc.local dombarker@100.108.41.90 \
  'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  QuadraticSpecializationOdd quadratic-specialization-odd-nuc-v1'
```

The runner used Lean 4.32.0, `-j1 -M9500`, MemoryHigh 8GiB, MemoryMax 10GiB,
MemorySwapMax 0 and CPUQuota 200%. All 823 overlay artifacts passed the
before/after provenance checks. Native package compilation remains a
pinned-revision cache boundary. The connection used Tailscale; only the host
key alias was `nuc.local`. The sole V8 build slot was released after the run;
no concurrent V7 process was interrupted.

H-specialization zeros still need an explicit bound or a proved elimination.
The fixed decomposition's existence and degree budget, factor classification,
and acceptance-to-actual-polynomial-root/source implications remain separate.
This finite count is not a global security theorem or efficient witness
extractor. No production/Rust/transcript change, CU/prover measurement or
grinding contribution was made. The proof-body maximum remains 40282 bytes.
