# Decoder-free selected compact-suffix partition

Status: `CausalCoveredRecovery.lean` passed its first focused NUC check,
consuming the checked `SelectedCoveredRelation` dependency. All eight axiom
audits report only `propext`, `Classical.choice` and `Quot.sound`.

The new execution contains fixed received C1, the three later C2 helper
lanes, OOD data, ordinary component claims and public weights. It has no
supplied C1 coefficient tuple, `earlyC1 = some p`, exact received polynomiality
or decoder-success premise. Its virtual word is literally
`SelectedComponentGame.received`; its ordinary/image row prefix is literally
`GammaComponentGame.rowPrefix`. The reference-zero oracle interface follows
from that row constructor, rather than being supplied by a caller.

The checked exact partition is

```
selected compact-suffix acceptance mass
  = acceptance with no good quotient representative
  + acceptance with at least one good quotient representative.
```

A good representative is in the actual fixed-word quotient family, folds to
the actual adaptive final, has both literal carried image residuals zero,
and has zero literal transported ordinary row errors. Interpreting the
image equations as concrete original-code membership still uses the checked
OOD/chord data interface; the present uniform bound needs no such premise.
This is not a payment witness, an original-component
tuple, or a proof of efficient access to the representative. The second mass
is retained explicitly as `goodProbability`.

The first mass is bounded uniformly at each gamma using
`SelectedCoveredRelation.no_good_quotient_bound`, then averaged over gamma.
There is no additional gamma collision charge:

```
outsideCeiling(q,A) + 99*(3/|G| + 6/|A|) + q/|G| + 18/|A|.
```

The bound concerns all selected compact-suffix executions with no good
quotient, including those whose mathematical early-C1 object is absent.
Actual source replay/provider abort classes are not invented as zero-probability
events; they still require a source/extractor coupling. C1 is fixed before
lambda/chi, C2 at its permitted later boundary, then both words and claims
precede gamma. Inactive may depend on gamma; the strategy retains
kappa/tau/alpha/query/rho/later-response dependencies. No final is frozen
before alpha, and no gamma-dependent quotient family is moved before gamma.

The existing actual three-helper degree bound remains two, and the full
29-component claim-error degree remains 28. Neither is used to invent an
extra collision term here. The latter cannot be replaced by a quadratic
bound on C1 claims.

The next recovery obligation is the retained good-quotient class: connect
these compatible quotient candidates to pre-lambda component/semantic C1
candidates and to a bounded authenticated recovery/validator path. A good
quotient alone does not establish correctness of every component claim.

No production/parser/transcript messages change. Body size stays 40,282
bytes, with q22, canonical fields, the carried image gate, shifted ordinary
row powers and shifted query batch unchanged. No new CU/prover measurement,
work-security credit, full-view ZK or resource-bounded Fiat–Shamir theorem is
claimed.

## Focused evidence

Research pin: `f19673b4fe72cf74ae687a926eeae9d1e5a6a52e`.
Borrowed V7/V5 closure pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`;
Mathlib pin: `81a5d257c8e410db227a6665ed08f64fea08e997`.
The new dependent target passed with exit 0 in 3.11 seconds, peak RSS
6,869,984 KiB and zero swaps. The runner checked all 697 imported/new
artifacts before and after execution, with no changes. This records the
pinned native package-cache boundary, not a replay of package compilation.

```sh
ssh -o BatchMode=yes dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-covered-family.rfQFkf/run_covered_family_nuc.sh /home/dombarker/project-offloads/aspis-covered-family.rfQFkf CausalCoveredRecovery causal-covered-recovery-nuc-v1'
```

Lean 4.32.0 ran with `-j1 -M9500`, MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0 and CPUQuota 200%. This was the only new wrapper check;
no laptop compile, package-wide replay or unchanged regression was run.

Frozen source SHA-256:
`0b1481e109d14c01be3ce6adbc0120106b6f830503a6bee96b48bae2fa4c6b35`.
Green olean SHA-256:
`44a4009624f02db9831ef631d973797c2023bab73e854509e7189dc6c461c5f0`.
Per-run manifest SHA-256:
`b68cd9670aedff5d9531dfe570fb662887e7cc555abba426d6fe88bcd63b3b17`.

The newly consumed selected family-bound source is
`1bee7a12268df16888d27d4a48b0651f098227af587877d6c0c3d854285a6e7f`,
with olean `2ea89e872a67f44863f6be6760ab8ccd922304bf000079994afc8257125b0317`.
Logs, manifests and the green wrapper olean are available in `experiments/`.
