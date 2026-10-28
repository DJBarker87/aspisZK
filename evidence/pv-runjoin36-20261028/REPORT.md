# Runjoin36 — h7 extraction blocked before Lean emission

Exact worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`; unchanged branch
`codex/pv-runjoin-20261026`; entry `1135ec947f86a1d3e375092b9f99e3b5db6fc164`.
The privacy target is not established. No ledger row or endpoint premise was
removed, added, weakened or otherwise changed. No shipped source, importer proof
text, shared source/cache, wallet or account was changed. No push or merge.

## Requested step 1

Regeneration was attempted, but **did not produce Funs or Types**. Consequently
`R1Z.ProverCommitOracle55` was **not re-elaborated**. This is an extraction
blocker, not an importer elaboration failure and not evidence of a historical
importer inconsistency or a counterexample to the shipped privacy claim.

The unchanged retained Stream B extractor binaries were verified against
`evidence/pv-cb3-20261026/retained-extractor-pins.txt`: Charon
`daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`, Aeneas
`562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19`.
These are the retained Stream B pins, not a claim of identity with the older
historical selected-mask Aeneas binary `959659a6…`. Both executable paths from
that older receipt are absent. Discovery and output absence are recorded in
`tool-discovery-and-output-status.json`; no alternative tool was promoted to the
historical pin and no extractor was rebuilt or patched.

Fresh private extraction inputs were frozen from entry HEAD. The existing
private Rust workspace was rejected because its aspis-prover/Cargo.toml differs;
it was retained intact. Exact source hashes are in `input-source-pins.json`.
The copied source root is recorded there, and all extraction commands are in
`*-command.json` and the per-phase receipts.

Cargo 1.94.1 resolved the actual shipped client root
`tools/r1-cost-probe/Cargo.toml` with
`r1p-check,aspis-r1-cost-probe/ct-host-prover`. Its full resolved per-crate graph is
`deployed-feature-graph.json`, embedded in every phase receipt. The reached
statement crate selects r0,pool-v1-kernel; its core dependency selects
r0,ct-host-prover; the three writer-copy dependencies select no features.
The extraction selects these explicitly, in release (opt-level 3, debug
assertions and overflow checks off for these reached packages). It does not
select the historical probe's overflow-check override or audit features.

Extraction uses the pinned Charon's **nightly-2026-06-01**, rustc 1.98.0-nightly
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. The deployed client toolchain
remains **1.94.1**. Exact versions are in `toolchains-and-initial-llbc.txt`,
referenced by every receipt. No nightly-to-shipped native-link body-identity
claim is made; that separate audit remains pv-fscan2's work.

Charon successfully extracted frozen
`pool_v1::pair_forest_semantic_terminal::terminal_parts` and its cone, with
built MIR and deployed features. The immutable LLBC has `has_errors=false`.
Aeneas then exited 2 **before emission**, with this exact exception:

```
ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires loan validation; structured Drop requires destructor semantics
```

The original log is `aeneas/out.log`. No guard was disabled. To isolate the
failure, a changed Charon request replaced the broad `aspis_core::field::*`
include with only M31, CM31 and QM31 carriers, preserving source/features/profile
and tool pins. This is a changed-input isolation, not an unchanged failed retry.
Its error-free LLBC was also rejected with the same exception; original log
`aeneas-narrow/out.log`.

`preflight-diagnostic.json` names the rejected declarations and source spans.
The first LLBC has two reference-returning signatures and 34 functions with
structured Drop; the isolated one has one such signature (core array Index)
and 30 functions with Drop, including composition_parts and the projected
Poseidon evaluator. These are read-only LLBC diagnostics, not a substitute
semantics or fidelity proof. Both LLBCs are retained compressed, with original
SHA-256 files. No generated Lean was edited, stubbed, selected from an older
variant or installed as the cone's authority. `importer-status.json` pins the
unchanged importer and explains why no replay was submitted.

## Validation and budget

Every actual phase was admitted only on allowed:true AND exit 0, then ran alone
in a scope with MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64. There was
no reservation refusal, timeout, memory kill or raised cap. All swaps are zero.
No native differential, Kani, Lean, unchanged full regression or release replay
was run. Axioms are N/A: no Lean theorem was newly accepted. The original
per-phase outputs and receipts retain commands, source revision, features,
toolchain reference, cgroup controls, wall, RSS and swap.

| Target | Exit | Wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- |
| deployed client Cargo metadata | 0 | 0.201 | 100192256 | 0 |
| frozen terminal Charon | 0 | 15.191 | 1297723392 | 0 |
| Aeneas translation | 2 | 0.402 | 152707072 | 0 |
| isolated terminal Charon | 0 | 16.805 | 1297694720 | 0 |
| isolated Aeneas translation | 2 | 0.302 | 114802688 | 0 |

The allocation 54400–54499, including audits 54497–54499, is untouched:
**0/100 Lean attempts, 0 Kani**. `id-inventory.json` checks sent.txt and the
other privacy jobs' receipt names. This is **budget unspent**, not exhaustion.
The scope wrapper's first metadata submission had an own-input Python keyword
error before launch; it was corrected under local-lean rule 11. No compiler was
started by that failed submission.

## Dependent work and retained obligations

Step 2 was conditional on successful step 1, which has not happened. Therefore
no current-emission SemanticOracle/security-oracle association, interpolation,
round threading, commitments/openings or complete proof serialization is claimed.
Step 3's actual runtime, both complete decoders and RustRealRefinement composition
remain incomplete. V038, V045, V163, V165 and V167 remain; whole rows removed: 0.
All eight PV_RunJoin_Premises fields are retained. T remains exactly entropy_law,
entropy_kernel, observation; no missing source/native fact was added to T.
The simulator, observer, coupling and bad/query events are unchanged.

The prior checked merge/sample/serializer/runtime-initialization results retain
their prior scope; none is promoted to a whole-prover or native result here.
D188 fidelity, native worker effects, allocations, TLS, filesystem/oracle effects,
Drop/unwind, failure worlds, deployed feature/profile/ABI and K-1/K-2 obligations
are unchanged. `boundaries-unchanged.json` records empty shipped/endpoint/ledger
diffs from entry HEAD. No recount or endpoint removal is claimed.

The affected h7 step is stopped at the mandatory unmodified-extractor preflight.
The historical pinned executable is missing at its recorded host path; the
retained Stream B binary's rejection cannot be repaired by disabling its guard,
changing generated output, modifying importer proof text or silently selecting
a different extractor. The lead has been asked for a restored historical binary
or an explicit extractor-selection ruling. Local-lean rule 5 assigns host/tooling
repair to the lead; dependent steps cannot be honestly advanced through this gap.

Next deliverable: resolve the pinned-extractor availability/selection and its
unsupported reference/Drop cone, obtain untouched regenerated Funs and Types,
then re-elaborate the unchanged ProverCommitOracle55 and report the actual result.
Only success permits the requested whole Result comparison and subsequent
runtime/decoder/refinement composition.
