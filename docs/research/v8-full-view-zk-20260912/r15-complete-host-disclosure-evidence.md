# R15 complete host replay and controlled same-public disclosure

Date: 2026-09-19. Privacy branch base:
`de6448dca91d39ecc55d5d60fa95a0ae53f4e6eb`.
Underlying source revision: `9e432896a4e1515efebe940b71fd9b4f9f009189`.

## Result and limits

The recovered host-only source subset **builds and runs** without the three
missing verifier/transaction-harness preimages. The uninstrumented restored
host generated a complete 39,554-byte proof; all ten semantic rounds checked,
the host verifier accepted, and nonce-search attempts were zero. This used
the host's **synthetic account-binding mode**, not a live account context,
SBF verifier, transaction or deployment. It is not a source security theorem.

A separately named research harness then generated two complete 38,878-byte
proofs for the valid duplicate-commitment witnesses. Their `public.bin`,
`transition.bin` and `binding.bin` match byte-for-byte. Both are accepted by
the same host verifier under **one fixed deterministic function** (SHA-256
with six explicitly listed output cells replaced). Both return the same
22-query schedule containing q4/q6. The statistic read from their actual
serialized C1 openings is respectively **907900822** and **1398498734**;
the difference is the retained **490597912** certificate value.

This demonstrates that the raw disclosure survives the complete source-derived
semantic/PCS construction and host verification in this controlled experiment.
It is not just an isolated encoder matrix. It does **not** establish the mass
of that event under the intended entropy-backed shared random oracle, any
actual SHA-256 attack probability, global privacy, or a production repair.

## Source and oracle discipline

`tools/stage_r15_host.py` archives a bounded source subset directly from the
target Git revision into a **new** directory, reconstructs the seven inputs,
and checks every resulting hash against `integration-inputs-v4.json`. The
selected performance SHA is `5ded…08d456`. No missing preimage is repinned.
Cargo metadata and the compiler dependency file contain no dependency on the
three missing verifier/transaction-harness files. This is host-only closure,
not the original complete transaction build or historical binary reproduction.

`tools/stage_r15_controlled_host.py` makes only these explicit test hooks:

1. In the fixture, use `two_outputs(leaf,leaf)` and select either existing
   witness with `ASPIS_R15_SELECTED_SECOND`. Public/root construction remains
   the source construction.
2. Route the host hash through `r15_controlled_oracle.rs`: a single fixed
   function table, shared by proof construction and verification. The table
   is loaded once; it never changes during an execution.
3. Print the existing q22 entry state and returned queries without changing
   the query sampler or its state progression.

The performance algorithm, mask inventory, semantic evaluator, serializer,
query sampler and verifier code are unchanged in this test copy. Main branch
and privacy-branch production source paths are not edited. The harness still
uses the source's deterministic fixture entropy, **not** the intended OS
entropy adapter. No hiding assumption is added.

Two SHA-only executions first locate the query entry addresses. The runner
then freezes the **union** of both three-cell tables before either final
execution. Both final worlds run from scratch against that same immutable
function. Query entry states are checked unchanged from the respective SHA-only
runs. Advancing uses SHA(state || 0x02) at the same old state as the replaced
squeeze input (state || 0x01). No earlier oracle answer is overwritten during
either final execution. This construction selects a function; it does not
sample the real random-oracle experiment.

## Exact execution evidence

Compiler: `rustc 1.93.0 (254b59607 2026-01-19)`;
Cargo: `1.93.0 (083ac5135 2025-12-15)`. Builds were offline, locked, optimized,
one job, with the `SOURCE_MANIFEST.json` host cfgs and features. They reused
`target/r15-pinned-host`; the second source-stage path required recompiling
the two local dependencies. No SBF/global build or dependency download ran.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Restored host release build | 0 | 85.99 | 738721792 | 0 |
| Uninstrumented baseline proof | 0 | 12.15 | 218316800 | 0 |
| Controlled host release build | 0 | 81.25 | 737820672 | 0 |
| SHA locate witness 0 | 0 | 12.10 | 218152960 | 0 |
| SHA locate witness 1 | 0 | 11.71 | 218218496 | 0 |
| Fixed-function witness 0 | 0 | 11.68 | 218071040 | 0 |
| Fixed-function witness 1 | 0 | 11.71 | 218218496 | 0 |

All four controlled subprocess exit codes were explicitly captured as zero
by the original runner and emitted to the tool output. The revised analyzer
does not invent missing old `.exit.json` files: its archived JSON marks those
fields null and points to this original-command evidence. Future runs persist
the exit metadata. All four accepted logs, timings, public/proof hashes,
test-hook source hashes and six fixed input/answer pairs are retained in
`evidence/r15-controlled-host.json` and `evidence/r15-controlled-*.log`.
No Lean target changed or compiled for this host replay; axioms are not
applicable. The separate universal extension leaf's audit is in
`r15-universal-disclosure-evidence.md`.

Baseline binary SHA-256:
`65a7f06b1ba5a9d3c787ee8d40f83d25316d363b5415a8c19a1466f6a6383a1a`.
Baseline proof SHA-256:
`9459b4fa31ce7758d2fd4acfe8f21d85a11d88e68acdcc6437d1de058a40411c`.
Controlled binary SHA-256:
`47f20ed77143245a667136c8f90644fda7d3b091c2fe6e5768debfe5291bfd93`.

## Retained analysis failure and correction

The first runner completed **all four host executions successfully**, then
exited 1 because its postprocessor incorrectly read the first four C1 fields
as four slots of column zero. The source `c1leaf` is slot-major, with 26
columns per slot; the correct bit offsets are `31*(slot*26)`.
The incorrect statistics were 359792617 and 1072365181. No proof or protocol
code was changed to repair this analysis error.

The reader was corrected and the existing bodies/logs were analyzed with
`--analyze-existing` (exit 0), without repeating the unchanged host executions.
Two new wire-reader controls pass: exact slot-major extraction and invariance
to schedule reordering/unobserved columns. The source negative controls
inside the host verifier run also remained enabled.

## Reproduction

From the privacy worktree, select a new staging/output path:

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/stage_r15_host.py \
  --repo "$PWD" --output /NEW/PATH/baseline-source
python3 docs/research/v8-full-view-zk-20260912/tools/stage_r15_controlled_host.py \
  --repo "$PWD" --output /NEW/PATH/controlled-source
```

For each stage, read its `r15-stage.json` (or `r15-controlled-stage.json`),
set `RUSTFLAGS` to the exact `rustflags` field and run:

```sh
CARGO_BUILD_JOBS=1 /usr/bin/time -l cargo build --offline --locked --release \
  --jobs 1 --features insecure-spend-fixture,selected-v7-kernels \
  --manifest-path /NEW/PATH/controlled-source/docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml
python3 docs/research/v8-full-view-zk-20260912/tools/run_r15_controlled_host.py \
  --binary /PATH/TO/aspis-v8-performance-host \
  --stage /NEW/PATH/controlled-source --output /NEW/PATH/runs
python3 docs/research/v8-full-view-zk-20260912/tools/test_r15_wire_statistic.py
```

Actual retained staging/run root is `/tmp/aspis-r15-host.drHYn9`; no task
artifact or key was deleted. The standalone baseline binary is also retained
there as `baseline-host`.

## First remaining proposition

Replace neither the chosen function nor fixed entropy by a uniform law by
definition. Establish the actual fresh-address/shared-oracle and stopping
law of an explicitly source-bound entropy-backed witness interface, and
account for all post-query failures/publication. The known ideal pair mass
is not yet an actual advantage bound. The host replay removes a local
execution obstacle; it does not close that probabilistic refinement or the
separate full posterior/simulator obligations.
