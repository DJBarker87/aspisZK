# Ledger refresh 8 handoff

**281/599 CLOSED, 0 QUALIFIED, 318 OPEN. Target not yet established.**
Branch codex/cx-ledger8-20261105. No push, merge, shipped-file change, new theorem,
Kani run or extraction. NGJ_LEDGER.json is committed as .json.xz with the raw SHA.
NGJ_LEDGER.md, NGJ_ROUTES.json and NGJ_TRUST_USED.json are the readable ledger,
per-occurrence routes and explicit accepted trust inventory/use table.

| Slice | Rows | CLOSED | OPEN | Roots CLOSED |
|---|---:|---:|---:|---:|
| S | 97 | 97 | 0 | 7/7 |
| Q | 161 | 145 | 16 | 2/2 |
| D | 345 | 43 | 302 | 0/1 function, 0/2 occurrences |

Four S/Q occurrences overlap and count once globally. Pool has no consumer row
in this verifier inventory; its production association remains OPEN. The D47
expectation does not reproduce: three old NFQ credits move to Q on the NGB
membership; NFT12 and NFU14 overlap at TX1:342. D = 21-3+12+14-1 =43.
Global =167+89+12+14-1 =281. NGJ_COUNT_RECONCILIATION.json names each moved row.

## Established claim and validation

All nine unchanged validators reproduced (NFX, NGB, NFT, NFU, NFY, NGE, NGF,
NGI, NFV), with writes isolated under NGJ_replay_outputs and sparse/compressed
inputs hash-checked. No validation predicate was weakened. NGF's packed
inventory was transparently decoded after its first missing-input finding.
NGJ_FROZEN_BODIES.json verifies every one of the 599 bodies at frozen
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. C0032 is now ADMITTED through the
unchanged NGB apply producer and NGJ_OVERLAY/EDGES: one reviewed callback edge,
compiler MIR plus source AST corroboration, no new row (callee already TX1:310)
and no slice membership change. NGB's five missing TX-specific paths remain
disclosed; union membership is not physical same-run reachability.

The ONE requested all-slices aggregate FAILED. NGJ_L002 finds duplicate SDK
GuardBody ownership; minimal pairs L027/L028 reproduce both GuardBody and
Prepared/PrepQM original-vs-RPz7 conflicts. L029 also exposes original/canonical
Phase ownership under verifier precedence. NGJ_CONFLICTS.json gives exact
names, module-table import paths and object/sidecar SHA256 provenance. No slice
was patched and no declaration renamed. No existing verifier row is qualified:
the verifier-only aggregate independently passes, while Pool's joint claim was
already OPEN outside the 599 rows. The failed full import is never promoted.

Verifier-only L003/L026 and raw audits: 4167 selected roots,
standard axioms only, zero collectAxioms disagreement, all 8 planted/mutation
fixtures in the SAME compiled proof binary. The full 13,375-module scan
(688,352 declarations, 24,396,032 references) has zero dangling
references, incompatible owners or import mismatches. Compatible replicas are
explicit (1582). All72 named D certificate references
are present in the raw manifest; NGI's complete261-name/19,364-record S
association checks reproduced. No name-filter omission creates credit.

The separate historical Pool precedence imports (L030), raw-walks 103 roots
with standard axioms and its same-binary8 fixtures, but L037 FAILS scanning:
650 dangling references, 0 incompatible owners,
548 import-baseline failures (524
absent independent baselines and 24 differing
lists). No zero-defect Pool/all-slices result is claimed. NGJ_SCAN.json keeps
all defects; exact selected environments are pinned separately.

NGJ_STATEMENT.md quotes the full existing S/Q statements and exact #print axioms
from L038/L039; every S statement matches NGI byte-for-byte. L040 quotes the
headline and representative D domains. NGJ_SHORTEST_PATHS.md gives ordered
necessary OPEN driver chains for TX1 and TX2 and distinguishes call paths from
execution CFG/acceptance coverage. NGJ_REMAINING.md covers Pool B/D and
L159/L181/L187/L188. All16 own evidence mutations are rejected by NGJ_TESTS.json.

## Assumptions and release boundary

No assumption discharged, added or removed. Retained: P6/D188 option-A native
contract semantic transport (reclassification), std/allocator/SDK/ABI/compiler/
Aeneas/source-to-ELF realization, RuntimePersistence, digest/H realization,
RuntimeReturnData ACCEPTED on nonempty 1..1024 replies (ASR8=792), RuntimeMemcmp
ACCEPTED on its exact 688-byte contract, and cryptographic assumptions. Pool A's
(af) std/allocator disposition is reclassification, never a copied-prefix proof.
Routes:267 (y),4 (ad),4 (ae),6 source reclassifications; no (ah) certificate
is supplied by this checkpoint. L154 is a statement parameter; coherent digest/
error slots are op43/op44. Privacy, two transactions and the 100-bit PER-ATTEMPT
release target are unchanged. This is a focused cached hybrid-certificate
checkpoint, not a cold release replay or deployed-security theorem.

Crates/programs are byte-identical to frozen 4bb3b3f5; no ELF rebuild trigger.
Inherited ONLY, not rehashed/rebuilt by NGJ: default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Resources, receipts and restoration

**40/40 slots used**: {'lean': 14, 'audit': 22, 'link': 4};33 success,7 recorded failures.
Failed shapes: missing Pool subroot input L001; full owner conflict L002;
missing4 owned import baselines L009; minimal owner pairs L027/L028; Pool Phase
conflict L029; legacy Pool scan L037. Prelaunch input/parser corrections are
recorded separately and launched no prover. No timeout, memory kill, cap raise
or unchanged timeout retry. Every launch had admission exit 0 AND allowed:true,
one own scope at a time, MemoryHigh6G/MemoryMax8G/SwapMax0/TasksMax64,
Lean -M7000; optimized -O3 audit linking. Wall sum 327.740s;
peak RSS 6,989,176KiB; swaps0. Exact target, command, source revision/
hash, dependencies/Aeneas pins, exit, wall/RSS/swap and axiom output are in
NGJ_ATTEMPTS.jsonl and the 40 linked receipts. Zero remaining Lean/audit budget.

Owned cache retained:
/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104 (8.3GB).
Initial coherent seed 30,032 paths /7,572,608,963 logical bytes; small D/Pool/
fixture supplements are separately hash-pinned, with identical bytes deduplicated
only within the owned cache. Source caches were read-only; no other worktree
was touched. NGJ_CACHE_IMPORTS and supplement manifests retain every imported
hash. NGJ_EXPORT.json retains 19 own compiled/native exports; NGJ_CLOSURE_PINS
and NGJ_POOL_CLOSURE_PINS pin actually selected closures, including Aeneas
objects/sidecars. Restore own NGJ_exports_20261105 first, then the exact recorded
verifier or Pool precedence; the two environments are intentionally distinct
and their coexistence is NOT claimed. No cache or key was deleted.

NGJ_HOST_END.json records hash-verified removal of owned rebuildable objects/
native binaries and raw graphs after export/local graph archival; all sources,
compressed graph evidence, receipts and retained cache remain. Large/repeated
source snapshots are stored once by SHA256 via NGJ_PACK.json; .REFERENCE.json
records resolve the original exact bytes. No file exceeds20MB; no Python
bytecode, object, binary, ELF or tarball is committed.

Next deliverable: canonical Pool forest retarget/replay with provenance and
zero-defect owner/reference/import scan, followed by production B/D same-execution
admission/settlement association. D's entry roots and all incoming domains remain
OPEN, then L159/L181 realization, L187 cold coherent replay, and L188 final
trust/axiom/source/artifact audit. **target not yet established**.

Stage commits:9e50ca5f402 (scope), bae97461a3e (reproduced ledger); final audit/
statement/handoff stage is the commit containing this file. No push.

Final hygiene: NGJ_ARTIFACTS.json PASS checks 4381 compressed/raw SHA pairs, 56 packed source references, all 40 receipt IDs and all 13 requested output names. Host cleanup hash-verified 4297 owned rebuildable files (1,216,212,619 bytes); all 19 exports and the owned cache remain, with no active owned prover. No wallet/key action occurred. Machine client/barrier logs are retained compressed with raw SHA256. Authored source/Markdown/Lean whitespace checks pass.
