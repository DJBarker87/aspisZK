# Selected higher-Y singular OOD pair mass

Status: **kernel checked**. The focused leaf is
[SelectedSingularPairMass.lean](experiments/SelectedSingularPairMass.lean).
Both printed theorem audits use only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry` or new axiom.

## Exact event and causal fixing

For fixed authenticated C1/C2 words, the selected singular-family theorem
constructs one nonzero obstruction polynomial `E` before either OOD draw and
proves

    natDegree E <= 25,345,827.

`exists_complete_root_set` constructs the complete finite set

    S = { t | source secure-circle parameter t is admissible and E(t)=0 }.

Thus `S` is fixed before both sequential samples. It is not selected from the
sampled points and does not condition on decoder success. The theorem retains
ordinary decode failures, inner retry exhaustion, duplicate exhaustion and
outer abort as zero accepted mass through the previously checked
`RootSetPairMass` kernel.

Given the kernel's history-uniform one-call law, including at the
answer-dependent history before the second point,
`selected_pair_root_mass_numeric_le` proves the unconditional bound

    targetMass(S)
      <= 25,345,827 * 25,345,826 / (N * (N-1)),
    N = (2^31-1)^4 - (2^31-1)^2.

The exact reduced rational is

    3244499600849 /
    2284408317668028910234756318256429327990468779241285843698658142054252544,

approximately `2^-198.8095102474`. No independent-label premise, successful-
sampler conditioning, nonce-search restriction, or work multiplier appears.

Composed only as an arithmetic screen with the separately checked singular
gamma numerator `117,049`, the pair term is negligible: the two terms sum to
approximately `2^-107.1632469139`. Adding one `q/(k-1)+18/k` suffix-repair
charge gives approximately `2^-107.1627539756`. That screen is not a global
ledger entry until event precedence and the actual oracle/source coupling are
proved.

## What remains outside the theorem

The history-uniform finite-coin law is still an explicit ideal-game premise.
The existing deterministic nested sampler refinement proves source/controller
equality on each tape, but it does not prove that actual domain-separated hash
callbacks supply fresh uniform tapes after adversarial prior queries. The
resource-bounded Fiat--Shamir theorem must retain prequeries, retries,
restorations, forks, and transcript selection.

The theorem bounds the singular pair-root alternative only. It does not prove
regular higher-factor extraction, payment-witness recovery, authentication,
full-view zero knowledge, or production acceptance. It changes no verifier
operation or proof byte; the body remains 40,282 bytes.

## Focused proof history

Attempts v1--v10 explored a direct selected filter and then a generic
admissible-root wrapper. The polynomial cardinality part compiled, but
elaboration of the deeply nested QM31 decidable predicate overflowed recursion
at the selected membership projection. Raising recursion depth did not change
that shape. The retained repair exposes the complete finite set by its exact
membership equivalence and applies the already-checked mass kernel to that set;
it does not unfold the nested predicate during the arithmetic proof. V11 was a
runner preflight collision after a restored green dependency and did not launch
Lean. V12 passed.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SelectedSingularPairMass selected-singular-pair-mass-nuc-v12
```

V12 exited 0 in 3.20 seconds with peak RSS 6,873,416 KiB and zero swaps.
The cgroup used MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPUQuota 200%, Lean 4.32.0 and `-j1 -M9500`; both 949-entry provenance checks
passed unchanged.

| Artifact | SHA-256 |
| --- | --- |
| Source / v12 snapshot | `dbca042e0a10d2a34c004a15652066b27d6df84399245f5a706dea8035552299` |
| Olean | `358e1615c863a8915167b2e4c7cfa07f93a6bf1e9f707d88133656963a01866f` |
| V12 manifest | `90d062a5224c27b7db77502bc771cf51b852649f85c50d8c6161b042b4dc97f1` |
| V12 log | `bf5c7f9d3c2b8d12b9ce128b86545be84c6d6c1701e6f2ba4d35e76d08fde387` |

The next soundness consumer should combine this pair event and the 117,049
singular-gamma event exactly once, then keep the regular alpha/query moment and
payment-extraction alternatives disjoint rather than summing overlapping
suffix repairs.
