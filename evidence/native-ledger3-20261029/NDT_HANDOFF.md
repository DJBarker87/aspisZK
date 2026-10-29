# NDT composition-ledger handoff

Authoritative snapshot: `NDT_LEDGER.json`, pinned research `f4ff4b340c06640d911632d110d49aa92e68e50e`; frozen Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Research still matches the cutoff at final audit (`NDT_HEAD_CHECK.json`). No push.

## Exact result and assumptions

All 587 inventory occurrences and 434 unique frozen functions are reconstructed and their frozen body spans rehashed. Admit 38 LOCAL CONDITIONAL domains: NDE 18, NDL 3, NDN 1, NDI 5, NDH 10, NDM 1. They change 45 inventory occurrences. Reject 92 status promotions and explicitly reuse seven NDD domains in NDL. Full reasons, exact domains, theorem/source/receipt associations and hashes are in `NDT_LEDGER.md`, `refresh.decisions` and `claims`.

| Inventory | Conditional before/after | OPEN before/after | Quarantined before/after |
|---|---:|---:|---:|
| TX1 | 124/160 | 219/183 | 2/2 |
| TX2 | 119/128 | 121/112 | 2/2 |
| all_rows | 243/288 | 340/295 | 4/4 |
| unique_functions | 141/179 | 291/253 | 2/2 |

All 587 composed rows remain OPEN; unconditional CLOSED 0; trust-only body credit 0. Conservative terminal-OPEN-SCC reachability cover: 130 → 111 representatives. Highest-impact OPEN functions are qm31_pack_base4 (29 dependent rows), CM31::square and WideExact::square (28 each), Arity::bits (26), pow5 (23). This graph ranking is neither runtime measurement nor a sufficient proof set.

Each admitted claim retains its exact PacketDomain and PhysicalInterpretation, including same live native/cohort carrier, installed dictionary and source-call/loop association. The static hash/transcript claims retain the static backend and actual runtime digest interpretation. Caller-owned domains/effects, SDK/std/allocator/ABI/compiler/source-to-ELF and P6/D188 transport remain explicit. P6/D188 is the approved reclassification, never premise removal. No headline, protocol, numerical security, privacy or trust premise is newly discharged or added.

All requested decoder/KNF/KNG/TX2/checkpoint packets are reviewed and reused without double counting. NCV/NCX/NDB full native decoder joins remain OPEN. NCN valid64 domain extension lacks new deployed feature/body/parent association; NCJ/NCK/NCM model/step work does not instantiate enclosing native bodies. NDA retains coordinates[4], rhs and power on the SAME NCU prefix, plus append/digest/oracle premises and native caller identification. NDN wrong-tag E015, sparse-frame limitations, timeouts, compiler failures and unpaired diagnostics retain no closure credit.

NDR is admitted as the exact reused shared-environment result, not a native row promotion: `AspisR1.NDR_CombinedAudit.sourceOnHeadline` in `lean/NDR_CombinedAudit.lean` (SHA256 fdfd7c55f0b99a38a588bd0730878534f697d7f0e872e1529a4c89b560aeb794), NDR_A001 exit 0, standard reachable axioms. Original tree-realization/runtime binders, FixturePdaRuntime, base/stage/slot quantifiers, two TX1 results, same saved bytes/length and TX2 result remain. Five thin modules have aggregation-only checks, not standalone builds. Arbitrary non-None adaptive transport is unproved. NDP completes enumeration for the two older separate forests; final shared-cohort import-wide F-AXIOM review remains OPEN.

NDQ records the immutable deployed devnet verifier/current release hash mismatch. NDS records the frozen existing-state registry obstruction and unperformed deployment; current design selects a distinct fresh Pool-state route. Neither supplies current-verifier or runtime executable/catalog/budget association. L188/native release target is not yet established.

## Validation actually run

`NDT_validate.py` exit 0; wall 31.784100s; peak RSS 2011201536 bytes; swaps 0; tested revision `1bf24370a421e62aff8fb682472dea34107579ee`. `NDT_FINAL_RECEIPT.json` records exact target/argv/revision, script/scope/recipe/ledger hashes, dependency fingerprint and resources. It independently reconstructs and compares the entire JSON/Markdown. Source changes justified the prior checks; the earlier passing pre-support check is retained as `NDT_PRE_SUPPORT_FINAL_*`.

Extended NCZ/NDK suite: 53 checks PASS (`NDT_TEST_RECEIPT.json`, outer `NDT_TEST_RUN_RECEIPT.json`). Original NCZ mutation logic: 14 checks PASS on NDT (`NDT_NCZ_TEST_RECEIPT.json`); `NDT_NCZ_TEST_ADAPTER.json` records only ledger/output redirection and sparse-file fixture adjustments. Original validator/test files are unchanged. The original NCZ CLI also ran on the final NDT ledger: expected exit 1, 'merged report corpus changed; refresh evidence snapshot explicitly' (`NDT_NCZ_ORIGINAL_*`). The extended validator supplies the explicit refreshed snapshot and passes.

Evidence: 5328 reports searched, 10491 SHA256 artifact pins, 117 distinct selected native proof/control receipts. Exact positive/one semantic-negative verdicts, lock/source checks, all-workspace or COMPLETE isolated six-crate deployed feature graphs (including all twelve statement optimizations), native Rust archive/patch hashes and successful exact-name theorem sources/axiom audits are checked. Transitive local reference/stub/induction sources are pinned to matching successful receipts. NDI's full inner loop and initialization association and NDM's erasure pins are checked. Python validates indexed claims, not arbitrary prose; manual semantic/caller association and inherited coherent-cache/tool transport remain audited trust boundaries.

All Lean/native/compiler evidence is REUSED. New #print axioms: not applicable; no new Lean theorem. No Lean compile, Kani, Rust/SBF build, host/RPC access, deployment, cache/library mutation or wallet/key/account operation. Python peak RSS stayed below 2.1 GB. No shipped source changed; no ELF rebuild trigger. Every committed file is below 20 MB. Authored files pass whitespace checks; one extra terminal newline in original NCZ raw stdout is retained unchanged.

Rule14 quarantine is not lifted. All nine original harnesses are listed with exact receipt paths in `NDT_LEDGER.md` and JSON `quarantine`. KNF/KNG replacements remain separate active support; the original historical receipts cannot supply active credit. Mark/observer retain four quarantined occurrences.

## Remaining blocker and next deliverable

Finish packing’s actual raw-log-to-whole-reference transport; split CM31 square raw-factor/product observations and WideExact mixed-coordinate carrier association; resolve multiproof consumers. Then instantiate each caller-owned same-execution/domain/effect/physical certificate. Preserve the exact imported model dictionaries and static hash backends. Complete final shared-cohort import-wide axiom/trust audit and current-release deployment/runtime/source-to-ELF association before any release claim. No further proof or deployment budget is implied.

Stage commits: `2dc6527f76` scope; `8b21393d3b` current research inputs; `52dc2c3142` refreshed ledger; `1bf24370a4` support dependencies and original tests; final validation/handoff is the commit containing this file. All local; no push.
