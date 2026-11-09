# Documentation

R1 is the current implementation. Its verifier checks a private spend across
two Solana transactions, its 599 reached Rust functions each carry a verified
Lean statement, and the composed soundness theorem for the actual spend path
compiled on 9 November 2026 with standard axioms only; the release target,
100-bit classical soundness per attempt, is not yet established, and the gates
that remain are set out in the proof package. The R1 verifier ran on Solana
devnet on 29 October 2026 and has not been deployed to mainnet. V7, the
one-transaction design that preceded it, is kept as the previous design and
was never submitted to a public cluster. V5 is the finalized mainnet result,
with a verified private spend on mainnet-beta on 24 July 2026 UTC.

## R1 (current)

The [R1 proof package](r1/) is the place to start. Its
[README](r1/README.md) lists every file and where on the research branch it
came from; the [status document](r1/SOUNDNESS-STATUS.md) is the authority for
every figure, the [top-level theorems](r1/TOP-THEOREM.md) are printed in full
with a reading of each binder, and the [open gates](r1/OPEN-GATES.md) say what
still stands between those theorems and the release claim. The
[devnet run](r1/DEVNET-RUN.md) and the [build recipe](r1/BUILD.md) cover the
deployed program. The full evidence is on the `research` branch at commit
`07123926e88273271344977a3fdc26d1780cde14`.

## History: V7 and V5

The pages below describe the earlier designs and remain accurate as records of
them. V5 is a private-spend construction with Lean proofs, selected production
verifier paths translated with Charon and Aeneas, a byte-reproducible Solana
program and a finalized mainnet-beta state transition; its Rust-to-model
connection is complete through the initial relation value, decoded relation
tail and both final accumulators, and its final clean replay passed on 24
August 2026. Its source is no longer in `crates/` and `programs/`, which now
hold R1; the frozen V5 inputs are kept in [`../release/`](../release/). V7's
local runtime measurements and formal record are in the [V7 activation
record](research/v7-one-tx-activation-20260828.md), the [V7 formal
consolidation](research/v7-one-tx-formal-consolidation-20260828.md) and
[`v7/`](v7/).

## Layout

| Folder | Contents |
| --- | --- |
| this folder | Overview pages: how it works, formal verification, assumptions, code map, design history, V5 mainnet result (V5/V7 era) |
| [`r1/`](r1/) | R1 proof package (current) |
| [`v5/`](v5/) | V5 accepted source map |
| [`v6/`](v6/) | V6 one-fold theorem audit |
| [`v7/`](v7/) | V7 plans, theorem audits, gate checklist and download provenance |
| [`v8/`](v8/) | V8 gates and the direct-compression rejection |
| [`operations/`](operations/) | Pool operator runbook, verifier-registry specification, read-only profile, privacy cleanup |
| [`novelty/`](novelty/) | Novelty and cryptanalysis scans |
| [`research/`](research/) | Dated research and audit notes |
| [`reviews/`](reviews/) | Publication and security-extension reviews |

## V5 and V7 reading order

1. [How Aspis works](how-it-works.md) — the private-spend statement, proof
   upload, atomic transaction, and cleanup
2. [What has been formally checked](formal-verification.md) — what Lean
   checks, how selected Rust is connected, and what remains trusted
3. [V5 mainnet result](v5-mainnet-demo.md) — finalized execution first, then
   exact deployment, lifecycle, compute, and refund evidence
4. [Security assumptions](assumptions-ledger.md) — cryptographic,
   translation, compiler, and runtime boundaries
5. [Accepted V5 source map](v5/v5-accepted-source-map.md) — the 15 review stops
   from instruction dispatch through proof checks and the state update
6. [Code map](code-map.md) — broader concept-to-file navigation
7. [Formalization report](../paper/aspis-formalization/) — mathematical,
   Rust-to-Lean, security, and trusted-boundary record
8. [Construction paper](../paper/aspis-spend/) — earlier protocol and
   deployment description
9. [Design history and previous releases](design-history.md) — evolution of
   the V5 result and the earlier q18/g37 record

## V6 research

The [V6 one-fold theorem audit](v6/v6-onefold-theorem-audit.md) records the first
checked results and the unresolved security work for the proposed 30 KiB
B10/q16 profile. It is research work, not a released protocol claim.

## Evidence by layer

| Layer | Record |
| --- | --- |
| Maintained mathematical models and Lean proofs | [`AspisFormal/`](../AspisFormal/) and its [proof-status table](../AspisFormal/README.md) |
| Selected production Rust translated and bridged to Lean | [`aeneas-verif/`](../aeneas-verif/) |
| Exact V5 SBF and reproducible build inputs | [V5 preflight](../release/preflight/v5-production-freeze.md) and [frozen candidate bundle](../release/aspis-v5-tag67-frozen-candidate-v1/) |
| Finalized V5 mainnet transaction and cleanup | [mainnet lifecycle bundle](../release/aspis-v5-tag67-mainnet-v1/) |

Run the V5 lifecycle verifier from a repository checkout:

```bash
./release/aspis-v5-tag67-mainnet-v1/verify.sh
python3 tools/check_release_facts.py
```

The [V5 evidence-chain publication
review](reviews/v5-evidence-chain-publication-review.html) records the resolved
framing and release-integrity findings and the boundaries that remain open to
outside review.

The [14 August formal-security extension
review](reviews/v5-formal-security-extension-20260814.html) explains the new
false-acceptance and theft proofs in plain English, including what they still
do not establish for the deployed program.

## History

The earlier q18/g37 Tag-65 feasibility result is retained separately in the
[historical mainnet record](mainnet-demo.md) and
[`release/aspis-spend-q18-g37-mainnet-v1/`](../release/aspis-spend-q18-g37-mainnet-v1/).
It is not the current top-level release.

Design evolution and archived research are indexed in
[design history](design-history.md) and the [archive](../archive/README.md).
