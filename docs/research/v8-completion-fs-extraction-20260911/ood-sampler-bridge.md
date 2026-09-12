# OOD sampler source-constructor slice

This continuation constructs bounded sampler executions, not a new probability
bound. Production, q22, proof bytes and verifier acceptance are unchanged.

## New deterministic results

- `FSChallengeCanonical.challenge_canonical`: every successful literal QM31
  sampler result has exactly four limbs, each strictly below `2147483647`.
  The proof follows masked-word bounds, remaining-word invariants and each
  bounded rejection loop. It does not enumerate QM31 or assume canonicality.
- `FSOODSampler.run_circle` and `run_distinct`: a bounded causal `Script`
  executes the same nested candidate loops as the functional source-shaped
  sampler, with identical returned result, digest, complete full-256 cache,
  chronological log and fresh-tape cursor. Per-limb exhaustion aborts the
  candidate operation immediately; outer exhaustion and duplicate-point
  retries retain all consumed state. No cached answer is resampled.
- `FSV7OODSampler` instantiates the decoder using V7's exact tower
  `exactSecureCirclePointFromDecoded`, including inverse failure BEFORE CM31
  rejection. Four-limb assembly uses the actual `c0.a,c0.b,c1.a,c1.b` order.
  `challenge_assembles` discharges the added list-shape/range guard for every
  successful source-shaped draw. The canonical-assembly version passed a
  focused historical Lean 4.32 run through the parent runner.
- `FSOODPair.run_pair`: first point, then absorption of literal label 62 with
  `[0]` and 464 first-answer bytes, then the distinct second sampler, all on
  the same carried transcript. Valid history and append-only log are derived.
  This slice uses a **no-hash** answer strategy depending on the first point;
  it is not a general adaptive prover callback or the whole semantic verifier.

## Executed evidence

Local entry commands (Std-only, Lean 4.33.1, one job, 2048 MiB cap):

```
python3 docs/research/v8-completion-fs-extraction-20260911/FocusedLeaves.py --root FSOODSampler
python3 docs/research/v8-completion-fs-extraction-20260911/FocusedLeaves.py --root FSChallengeCanonical
python3 docs/research/v8-completion-fs-extraction-20260911/FocusedLeaves.py --root FSOODPair
```

Evidence under `results/v8-completion-fs-extraction-20260911/`:

| Changed leaf | Successful evidence directory | Wall seconds | Sampled tree RSS KiB |
|---|---|---:|---:|
| FSOODSampler | `FSOODSampler-_quxlqfx` | 0.715 | 710512 |
| FSChallengeCanonical | `FSChallengeCanonical-7x0qp0xr` | 0.472 | 701728 |
| FSOODPair | `FSOODPair-ww6x41_n` | 0.467 | 701392 |

All three exit zero. Logs retain exact `/usr/bin/time -l` peak RSS, zero swaps,
axiom output, commands and source hashes; manifests pin the source revision.
The only reported axioms are standard foundations. Failed local snapshots/logs
remain in earlier evidence directories. This is source compilation, not a new
fresh-kernel replay; historical-toolchain checks are separately parent-owned.

Parent historical-toolchain checks also passed `FSChallengeCanonical`
(0.35 s, 749,616 KiB RSS), the canonical concrete `FSV7OODSampler`
(3.20 s, 6,514,360 KiB RSS), and `FSOODPair` (0.45 s, 753,328 KiB RSS),
all at zero swap with standard axioms. The report-only receipt records the
commands and hashes; it is not an independent artifact rebuild.

## Remaining source and probability producers

The pure field map is reused, not reproved or imported from an unchecked pack.
Literal Rust/Aeneas refinement remains open. The first-answer bytes still need
the actual causal semantic producer, canonical encoding and same-body binding;
the pair slice has no second-answer absorption or later gamma/relation rounds.
Hash-capable answer production must use a bounded Script whose calls join the
same log rather than treating their absence as a cryptographic fact.

The remaining uniformity obligation is NOT simply 'each invocation is fresh'.
One must couple legal source continuations to the common uniform full-256 tape
at their **first exposures**, charge premature/collision alternatives using
the actual V7-style scheduler, and transport each cached/retry/abort branch.
Only then can exact bounded sampler distributions be applied. This task adds
no FS loss number and supports no global 100-bit claim.
