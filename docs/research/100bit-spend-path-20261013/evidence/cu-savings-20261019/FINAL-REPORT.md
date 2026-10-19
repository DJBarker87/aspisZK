# J1.R13 arithmetic worker final report — 2026-10-19

**PASS: both transactions are strictly below 1,200,000 CU on every saved fixture.** Highest stage 1: **1,199,687** (313 CU headroom). Highest actual Pool settlement: **1,188,496** (11,504 CU headroom). These are measurements of the six specified fixtures, not a universal input bound.

Side branch: `codex/r1-cu-savings-20261019`, based on `origin/research` `f458169f705f25b04e1e29546c621e4665e0f64c`. The root checkout was not edited. Only this side branch is pushed; the lead owns merge/archive.

Final producing Rust revision: `39c2971dd16c95858a4cfd2c9ae35da052eacfa9`. Executed ELF SHA-256: `a70f30bd567818ad1542cdebc519e81f4780b463726ff509c245a09b0cfea01a`. SBF features: `pool-adapter,private-leaf-salts` (resolved optimized-terminal bundle remains enabled; no prover). Internal phase/CU profiling is opt-in via `cu-profiling`; application result effects are preserved. No ELF or `.so` is committed.

| Fixture | Stage-1 transaction CU | Nested stage-2 verifier CU | Actual Pool settlement CU |
|---|---:|---:|---:|
| transfer-13 | 1,199,648 | 1,034,767 | 1,137,397 |
| transfer-255 | 1,199,567 | 1,034,718 | 1,174,671 |
| transfer-1023 | 1,199,687 | 1,034,688 | 1,171,579 |
| withdrawal-13 | 1,198,225 | 1,034,510 | 1,150,958 |
| withdrawal-255 | 1,198,264 | 1,034,675 | 1,188,496 |
| withdrawal-1023 | 1,198,386 | 1,034,477 | 1,185,236 |

Withdrawal 255 improves from 1,339,527 / 1,380,079 CU to 1,198,264 / 1,188,496 CU: **332,846 combined CU saved**. Original 1.3M target and the later stricter 1.2M user target are both met without moving the split.

## Measured candidates

Each candidate has its own source commit. Rejected implementations have explicit revert commits; their correctness/resource/CU evidence is retained. Savings below are **incremental versus the retained predecessor**; each candidate SUMMARY also records every fixture against the J1.R13 baseline. Negative numbers are regressions.

| # | Candidate | Decision | Stage-1 CU saved (range) | Settlement CU saved (range) | Source revision |
|---|---|---|---:|---:|---|
| 1 | Reuse gamma powers | KEEP | 34,201…34,243 | 0 | `3ab4faf7f` |
| 2 | Opt-in profiling | KEEP | 10,992 | 13,201 | `190e1779c` |
| 3 | Fixed S2 inactive groups | KEEP | 0 | 40,517…40,520 | `d631a90ec` |
| 4 | Delayed base-dot reduction | KEEP | 28,221…28,252 | 33,880…33,932 | `d11f9b2fc` |
| 5 | Private canonical dot operands | KEEP | 11,273…11,286 | 11,617…11,630 | `e58b87665` |
| 6 | Reuse decoded public statement | KEEP | 7,418…7,472 | 0 | `e5a93db5c` |
| 7 | Reuse query geometry | KEEP | 780…791 | 947…957 | `2aa1b879c` |
| 8 | Nine Karatsuba channels | DROP | -58,104…-57,829 | -79,768…-79,264 | `f40c80702` |
| 9 | Mersenne quotient correction | DROP | -32,905…-32,801 | 0 | `481df1dec` |
| 10 | Fixed 608-byte dot prefix | KEEP | 5,620 | 6,744 | `225a3736d` |
| 11 | Prepared three-term tails | DROP | -12,770…-12,678 | -15,308…-15,194 | `b0005af33` |
| 12 | Transaction-local rho residues | KEEP | 42,693…42,746 | 51,250…51,356 | `16a39d2a8` |
| 13 | Shared four-slot coefficient loads | DROP | -13,930 | -16,716 | `029206324` |
| 14 | Factored S2 Libra row | KEEP | 0 | 33,363…33,427 | `39c2971dd` |

## Required gates and evidence

Every measured candidate completed codec **1,233** byte-identical outputs; the exact ordered **583** cryptographic calls (**349/234**), including inputs and answers; checkpoint **23**; both relevant injection modes; one SBF build; strict linked-ELF stack audit; and all six saved fixture replays with both stages plus actual Pool settlement. Final focused gates also compare all four factored Libra weights on 512 arbitrary/edge cases and run the existing weights equivalence suite. Every run receipt records exact command, producing revision/source manifests, features, exit, wall time, RSS, swap and cgroup caps. No task Lean compile ran, so `#print axioms` is explicitly N/A on these runtime/source-only results.

Large/native builds ran under individual 6 GiB high / 8 GiB maximum scopes with `MemorySwapMax=0`, optimized release profiles and finite aggregate reservation admission. The user later authorized parallel NUC work; foreign host jobs were recorded. No own Lean job was launched. Successful unchanged gates were reused on harness-only retries; dropped-source reverts did not trigger unchanged full regressions.

The ordered trace is never sorted. Only the auxiliary repeated-input histogram is sorted for comparison because its HashMap iteration order is nondeterministic. Initial injection staging failures and receipts remain archived. Candidate 12 compares its transient rho residues through a **test-only canonical projection** before the old observation hook; final checkpoint bytes and real hash calls remain exact. The bounded-prefix differential establishes the representation invariant at every tested prefix.

## Readonly metadata runtime backing

**PASS: all 13 mutations reject inside the verifier; both controls pass**, pinned to ELF `4e1fd78fbddb39cb9599de7694105547d8e86e7451f8b9f3e9626789036e8711`. Each rejection preserves protected accounts and matches the phase afterstate expectation. The repair is driver-only and uses LiteSVM persistence-internal insertion for synthetic executable metadata; signature verification is disabled consistently for controls and negatives. This backs the selected `R16ReadonlyMetadataProjection` premise and makes no legal-state reachability, custody or signed-transaction claim. See `readonly/SUMMARY.json` and per-case receipts.

## Soundness source hygiene

Promoted the functional batch and subfield batch sources bytes-unchanged, and the c16 PublicPreparation Funs/Types (Funs `e98bb123…`) into the non-evidence Lean root. Added import-only R1 forwarders for SpendRelation, SpendAppendBinding and TraceAppend. Canonicalized the current split selected params/sampler/challenge-map owners, with unprefixed forwarders and explicit current support-module ownership. No Lean statement or proof body was edited.

The requested five-root unified manifest `--check` resolves **718 source modules and 92 library identities**, with **zero unresolved modules, source conflicts, alias collisions or cycles**. The check is at `6cf51b8f9`; its Lean inputs and tooling have not changed afterward. This local source check does not assert library object availability or a new compilation. **No unified compile was started.** See `hygiene/receipt.json`, source promotions and manifest output.

## Formal re-pin handoff

Every candidate carries `declaration-repin-inventory.json`. These list changed Rust owners, retained emitted Lean declarations, opaque/un-emitted boundaries and required equivalence obligations. Historical proofs are not attributed to different optimized bodies. New private arithmetic, rho representation and Libra factorization still require the indicated extraction/source-simulation re-pins before a formal release claim; this task does not claim those proofs complete. The canonical non-evidence source hygiene work is separate from that pending optimization proof work.

All task keys remain retained privately on the NUC (directories 0700, files 0600); future children inherit umask 077. No network transactions, cleanup, key destruction or refunds were attempted. No wallet secrets are included in the evidence.
