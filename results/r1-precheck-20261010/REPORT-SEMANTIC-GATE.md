> Historical semantic-gate report. Its missing-Libra blocker was resolved by
> the later PLAN clarification; see [REPORT-P2.md](REPORT-P2.md) for final status.

# P2 — UNPROVED R1 COST PROBE

Status: **incomplete; semantic byte-equivalence gate passed; opening work awaits
the definition of the Libra functional.** Neither S nor D has a measured result.
This is an isolated cost experiment, not a reference implementation.

Base: `origin/v8-reference` at
`600eb013878a0169cdab8f222e879cd395e3a1e2`.
Branch: `codex/r1-precheck-p2-20261010`.
The final two-transaction decision in
[`PLAN.md`](../../docs/research/v8-r0-rust-20261009/PLAN.md) is the task basis.

## Completed semantic gate

The new `aspis-r1-cost-probe` crate contains an isolated copy of the semantic
wire/transcript and a K-valued semantic verifier. It makes the two requested
changes:

1. Obtain the first four base-p digits of the 256-bit block directly. Those
   digits represent reduction modulo p⁴; the preliminary binary long division
   and the remaining four digit divisions are unnecessary for this output.
2. Assert that the E high component is zero during parsing, then evaluate
   degree-27 round polynomials, claims, the terminal and mask arithmetic in K.
   The public S4 `terminal_qm31` evaluator is reused without changing its source.

The retained S4 transfer and withdrawal proof/public files were read directly
from the R-E4 build-host results. They were neither regenerated nor changed.
Their SHA-256 values and sizes are in
[`artifact-manifest.json`](artifact-manifest.json).

| Native check | Transfer | Withdrawal |
| --- | ---: | ---: |
| Acceptance, S4 and probe | pass | pass |
| Semantic challenges, byte-identical | 25 | 25 |
| Transcript states after scalar rows, identical | 25 | 25 |
| Round polynomial coefficients, byte-identical | 280 | 280 |
| Round check values, byte-identical | 30 | 30 |
| Point-claim values, byte-identical | 87 | 87 |
| Before-z1 values, byte-identical | 29 | 29 |
| Terminal and masked terminal, byte-identical | 2 | 2 |
| Roots, alphas, z points, boundary/final transcript states | identical | identical |
| Nonzero-high-component parse mutations rejected | 397 | 397 |

The sampler gate compared 4,610 blocks (zero, all-ones, each single bit,
each complemented single bit, and 4,096 SHA-derived blocks). All K outputs
matched S4. Both circle mappings also matched on those blocks: 9,220 checks.
These are finite native checks. The 794 mutations cover only the semantic
high-component assertion; they do **not** satisfy the full P2 message and
checkpoint mutation gate.

Full results and trace hashes:
[`semantic-equality.json`](semantic-equality.json).
The test source is
[`semantic_gate.rs`](../../crates/aspis-r1-cost-probe/examples/semantic_gate.rs).

## Missing opening definition

PLAN's R1 outline names a **“Libra row (56 K entries)”** but does not specify
its 56 coefficient indices, entry formulas, claimed value, or how that value
is tied to the retained semantic messages. A search of the research Markdown
and state-only Rust found no additional definition of this row.

The existing row-14 mask total cannot be silently substituted. SPEC §9 calls
it a sum of `maskValueClaims`; `state_only_selected_mask_value` uses different
factors for semantic lanes 0–15, mask lanes 16–25 and G at lane 27, with zero
factor for D at lane 28. It is also distinct from the PCS inactive sum.

For a common coefficient weight w, the proposed batched polynomial gives

```
<w, f> = Σ_l γ^l <w, W_l>.
```

Using the old mask total here would require a specified correspondence between
its lane-dependent factors and this common w. The current outline provides
none. Choosing arbitrary 56-entry weights would change the relation being
probed and prevent a meaningful dense self-consistency comparison.

Clarification requested: the exact coefficient-index weights of the Libra row
and its claimed-value formula (including its connection to the semantic
messages). The opening prover, dense relation oracle and S/D measurements are
pending that definition. No zero row or invented replacement has been used.

## Measurement status

| Variant | Transaction | Phase CU | Total CU | Headroom to 1,300,000 | Proof/checkpoint bytes |
| --- | --- | --- | --- | --- | --- |
| S | tx1 | not measured | not measured | not measured | not produced |
| S | tx2 | not measured | not measured | not measured | not produced |
| D | tx1 | not measured | not measured | not measured | not produced |
| D | tx2 | not measured | not measured | not measured | not produced |

No k is selected. No full R1 proof has been produced. Acceptance ×5,
DIAGNOSTIC CU, SBF stack audits, heap checks, dense relation agreement and the
full mutation corpus remain outstanding. There is no per-configuration stack
audit JSON because no complete configuration has been built. This report
does not close the P2 fit gate.

## Resources and retained evidence

The single native gate used an optimized release binary. Compilation was the
expected dominant step. It ran in its own Linux systemd scope with
MemoryHigh = 4 GiB, MemoryMax = 6 GiB and MemorySwapMax = 0, after checking
aggregate reservations. It exited 0 in 38.04 seconds. Sampled aggregate RSS
peaked at 1,096,474,624 bytes; cgroup memory peak was 870,645,760 bytes; final
cgroup swap was zero. Neither a cap increase nor a rerun occurred.

See [`semantic-gate-v1.json`](semantic-gate-v1.json),
[`semantic-gate-v1.log`](semantic-gate-v1.log),
[`semantic-gate-v1-reservations.json`](semantic-gate-v1-reservations.json), and
[`semantic-gate-v1-source-manifest.json`](semantic-gate-v1-source-manifest.json).
The source manifest records the base revision plus exact dirty source hashes
used by the gate. The isolated build cache is under
`/home/dombarker/project-offloads/aspis-r1-p2-20261010/target`.

The native executable is retained only on the build host under
`results/r1-precheck-20261010/bin/semantic-gate-v1`; its SHA-256 and size are in
the artifact manifest. Committed evidence consists only of JSON, Markdown
and logs. No SBF, ELF, `.so`, `.text` or disassembly artifact is committed.
No Lean, reference prover, reference verifier or fixture path was modified.
S4 CU was not re-measured.
