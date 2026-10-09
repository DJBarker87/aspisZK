# Fixed-C1 execution: outside-family query reduction

Status: `FixedC1OutsideQuery.lean` passed its focused NUC v2 check and all
seven audits contain only `[propext, Classical.choice, Quot.sound]`. The
selected query theorem and all geometric dependencies were already checked;
only the changed execution wrapper was rerun. No laptop check was launched.

The leaf consumes the actual `FixedC1FarMoment.Execution`: fixed C1 and
`earlyC1 c1 = some p`, arbitrary three late C2 words, pre-gamma OOD and
ordinary component claims, a gamma-dependent inactive claim, and the
causally ordered strategy for each gamma/kappa prefix. It does not supply
a second convenient virtual word or an independent reference quotient.
`row_reference_zero` derives the actual row constructor's `referenceQ=0`.
Thus the oracle is exactly `oracle 0 (e.raw gamma)`, as in the previous
far-final game.

For each gamma/kappa, `outsidePrefix` is absence of the actual selected
final from the fixed quotient family with at least9,558 own-support fibres.
That family is fixed by the actual virtual word before alpha; the final
remains adaptive in tau and alpha. `outsideSlice` uses the literal compact
suffix probability, including the actual final-dependent carried prior,
shifted degree-q rho batch and sequential later repairs.

The checked `all_outside_bound` applies `actual_off_family_suffix`
uniformly and averages gamma/kappa. It assumes nonempty finite A, G and
Gamma, and `0<q≤262144`:

```
outsideProbability ≤
  choose(9557,q)/choose(262144,q)
  + foldChallengeCap/|A| * choose(117964,q)/choose(262144,q)
  + 127/|A| + q/|G| + 18/|A|.
```

This bounds all outside-family execution mass, so it requires neither a
wrong-C1-claim condition nor a gamma-root exception. In particular it does
not add another28/|Gamma| charge. The existing helper-curve degree≤2 and
full component-error degree≤28 results remain unchanged; neither is
silently substituted for the other.

The event inclusion is explicit, with the same nonnegative suffix mass:

```
farWrong ≤ outside OR (farWrong AND covered)
farProbability ≤ outsideProbability + coveredFarProbability.
```

The second term is not assigned a number. A quotient in this full-code
family is not automatically image-valid, a tuple of original component
polynomials, or a checked payment witness. The source-shaped theorem also
does not cover the `earlyC1=none` branch, which is absent from `Execution`.
The generic outside-family theorem can later be coupled to that branch
separately; this wrapper does not establish such a coupling.

No authentication/replay/Fiat–Shamir theorem or extractor runtime is added.
No transcript, proof field or verifier operation changes; the body remains
40,282 bytes. Proving and complete-transaction CU measurements are unchanged.

## Reproduction and evidence

Research source pin: `b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9`.
Borrowed source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The isolated NUC overlay's681 source/output entries pass before and after;
native package revisions are pinned, not newly replayed package builds.

```
ssh -o BatchMode=yes dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-masked-tail.SH0QtS/run_masked_nuc_selected.sh /home/dombarker/project-offloads/aspis-masked-tail.SH0QtS FixedC1OutsideQuery new-tag'
```

Use a fresh tag. The runner uses `lake env`'s cached Lean4.32.0 executable,
`-j1 -M9500`, `MemoryHigh=8G`, `MemoryMax=10G`, `MemorySwapMax=0` and
`CPUQuota=200%`. No simultaneous build ran.

| Run | Exit | Wall | Peak RSS | Swaps | Result |
|---|---:|---:|---:|---:|---|
| NUC v1 |1|19.12s|7,102,904KiB|0|Dependent reference rewrite failed type transport; conjunction simplification and final elaboration also failed|
| NUC v2 |0|3.27s|6,868,200KiB|0|All seven audits standard-only; full postflight passed|

The v1 source, log and manifest remain preserved, not claimed as proofs.
The v2 proof uses the literal constructor's definitional zero reference via
target-directed `change`, avoiding dependent casts from a broad rewrite.
The event split supplies exact conjunction/non-conjunction facts; the final
inequality composes named rational bounds. No theorem premise, challenge
order, recursion cap, heartbeat cap or resource cap changed in that repair.

Frozen SHA-256:

- Source: `33c5e38a4ec470a085507a1204c7a577d8068fa70d43514a38e7d5b4b70696c8`
- Olean: `934ecbedf3c8f6ac41345dd50a759c99f4e5a1245964f8f400607f14fae23f5f`
- NUC runner: `3cc0df9496329e9c373823966e9fda164dc0feae62083156d8dc90493ff0d6c1`
- v2 log: `8ed2505cb861a91058470a644183fd59f03887889d315c7e9c69c8e0c5770656`
- v2 manifest: `4c93d819a6c75ccb7e2452ff7402c0b6a1ed7c55a62a1a17f2cf35b89c64821f`
