# NFO handoff — Pool return-data association

Disposition: OPEN. No S2/S6/S10 composed row or headline is closed by NFO.
The packet is useful local evidence plus explicit findings, not a release result.

## Read first

NFO_INSPECTION.md (source/ELF path and error branches), NFO_BRIDGES.md (native
scope/control table and model limits), NFO_RUNTIME_SCOPE.md (SDK empty/capacity
finding), NFO_AUDIT.json and NFO_SCAN.json (FAILED aggregate gates), then
NFO_REMAINING.md and NFO_CONE_DELTA.md. NFO_ATTEMPTS.jsonl records every launch;
NFO_RECEIPTS.json indexes the exact commands/targets, exits, time/RSS/swap,
source revisions/content hashes, dependency pins and #print axioms. Compiler
errors/sorryAx in failed diagnostics are excluded, never imported or credited.

Frozen release source:4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Exact final hashes are rechecked in NFO_RETAINED.json:

* default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
* devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
* Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No repository crates/programs/shipped file changed. Native hooks/harnesses exist
only as committed cfg(kani) patches for the external scratch copy. No shipped
change means the three-ELF rebuild trigger was not exercised; hashes, not new
reproducible builds, were checked. No wallet/key/account operations occurred.

## Key results

The cited legacy verifier_dispatch.rs expects384 bytes; actual NFD ASR8 consumer
is pair_forest_dispatch.rs expecting792. Frozen ELF's successful invoke0x3eb0
is followed by read0x3ee8 with no intervening CPI/set; selected program is checked
before length/decode. Every rejection path is mapped in inspection evidence.
K007 read-cut and actual-caller rejection fixtures have matched failing controls.
K054 checks the source-exact decoder cut with all error variants and exact child
arguments. K056's account-meta/AccountInfo key associations FAIL; request-only
K059 and constructor K057 do not repair it. K006 generalized pointer equality
also failed; no shipped bug is claimed for either unisolated failure.

NFO_PoolReturnData.association and NFO_AcceptedAssociation.consumed compile with
standard axioms and explicit OPEN codec/native premises. Supporting serializer
layout/injectivity and accepted-packet/error laws compile. NFO_Final.codec_iff_raw
reduces the mathematical gap to the raw accepted inverse; no inverse is assumed
silently. Actual decoder extraction E001 is retained with NCO pins and exact
canonical adaptation manifest. Its19 external-template axioms stay text only.

## Verification and reuse

60/60 Kani,40/40 conservatively charged Lean/link/audit/scan scopes,1/3 extraction:
101/103 allocations used. No timeout/OOM or swap; maximum measured RSS5913072KiB.
All scopes used6G/8G/zero-swap/64-tasks caps, optimized Rust and Lean -M7000.
Only one scope at a time. Every Kani gate validates frozen graph, offline mode,
unchanged frozen lock and deployed feature lists. Exact KMX patch pinned, matching
negative controls retained; no writable statics or function-pointer quarantine
uses. No LPb stage or unrelated horizontal WIP was imported as credit.

The hardened walker is byte-identical to NEP_WALKER; full driver diff committed.
First fixture run lacked imported IR; identical cached IR companions were copied
with hashes, then eight fixtures/mutations reproduced exact expected results in
the SAME compiled driver as the final audit. All29 raw roots have only standard
axioms and zero unresolved reachable constants, but five NFO_ReadModel gate roots
have extra standard raw axioms versus collectAxioms, so final audit exits1.
Loaded scan:9334 modules,624252 declarations,21697536 edges,650 unresolved
references in15 imported modules; all18 NFO proof modules have zero. Entire scan
exits1; raw import lists retained, no independent import-baseline equivalence
claimed. Do not bypass either failure.

Own wrapper repairs are recorded by source/receipts: helper/signature fixes,
strict graph JSON parsing, actual launched-attempt count (not failed preflight
ids), scanner/IR/runtime binary pins and a serial fixture+final audit wrapper.
Reservation scripts/host launcher/shim/shared workspaces were never modified.

## Retained cache and next work

Own cache /home/dombarker/project-offloads/codex-cx-pool-retdata-cache-20261104
is retained, never deleted. NFO_HOST_PINS.json records copied inputs, including
NFJ objects first and the available compose10-20261029 path (the requested
20261104 alias was absent). NFO_IR_SIDECAR_PINS.json records exact companions.
NFO_RETAINED.json pins final source/object/sidecar files and audit binaries in
NFO_final_objects_20261104 / NFO_audit_native_20261104; only own rebuildable
target/tmp/object/native scratch was removed after terminal receipts. Restore
from these pins for a newly allocated focused continuation. No session-A or
sibling live worktree/cache was edited. No push.

Next deliverables: isolate K056 with exact KMX; prove RawInverse using existing
digest/afterstate accepted inverses and checked layout; close runtime Vec/carrier
and settlement/context associations; resolve audit/closure findings and runtime
empty-domain scope. More extraction alone cannot discharge these. Remaining
Lean work was not stopped because Kani ran out: Lean/audit budget is exhausted.
