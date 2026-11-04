# Ledger7 findings

Target not yet established. Frozen source and the per-attempt security contract
are unchanged. This is a correction to coherence credit, not a shipped bug claim.

## F1 — source-valid S packets are not headline-coherent

The faithful privately copied NFJ lookup order passes its standalone packet
import (L007). Adding the actual headline fails (L008): original
`PreparedFromQmSourceBridge.PrepQM` conflicts with the canonical RPz7 owner.
The separately loaded original S forest (L016) has exactly **650 dangling
references in 15 modules**. This reproduces, rather than waives, the inherited
NFO/NFR defect. Earlier failures under an incorrectly flattened lookup order
are own configuration diagnostics, not evidence for F1.

`NFX_S_PACKET_PATHS.json` follows actual measured module imports and exact
selected certificate references. It finds legacy paths for **85 occurrences**.
Four further occurrences lose their selected callee claims. All **89 become
QUALIFIED**, preserving their original source-validator CLOSED records.
All seven S root functions are affected (eight transaction occurrences).
Four independent helper occurrences and four shared Q/S occurrences retain
coherent credit. The conservative inventory and exact paths are retained.

No source validator or standard-axiom check is sufficient to override this
failure. Next deliverable: a prefix-owned canonical retarget of the affected S
packet forests and their concrete theorem/type associations, followed by the
same combined audit. No live session A candidate or worktree was edited.

## F2 — two inventory defects remain outside the slices

`TX2:046` is unresolved `WideExact::from_m31`; `TX2:211` is the omitted
`map_err(error)` callback. D ∪ Q ∪ S covers 585 occurrences, not 587.
Both defects remain OPEN, explicitly present in the ledger. D is the NFQ
canonical union closure: 295 functions, 448 internal edges, 343 occurrences.
Both transactions use the same deployed program-entry function. Six D rows
have only union-graph paths, not transaction-specific reachability proofs;
this refresh does not invent those proofs.

## F3 — no Pool or trust-row status inflation

RuntimeReturnData is ACCEPTED only for nonempty 1..1024-byte replies; ASR8 is
792 bytes. RuntimeMemcmp is ACCEPTED on the exact 688-byte domain.
RuntimePersistence and P6/D188 option A are retained. These statuses do not
close the Pool join. NFR established the accepted inverse and same-value MODEL
join; production prefix/admission, helper/carrier transport, account-meta/key
association under the exact (af) route, and a joint reachable execution remain
OPEN. NFO/NFR report no composed NDT row. No reclassification was silently
turned into an implementation proof.

The emitter/scanner now have no CLOSED direct trust consumer in this refreshed
ledger because F1 qualifies them. Accepted runtime trust remains in the final
headline context. L154 remains a statement parameter; op43/op44 are digest/error.

## F4 — canonical forest and common-library provenance

The final combined forest loads **13,126 modules**, with zero dangling
references, zero incompatible declaration owners and zero import mismatches.
All 263 selected raw roots have standard axioms and agree with collectAxioms;
the same binary passes all eight planted/mutation fixtures.

The old S packet roots, original Phase/Prepared owners, and
ExtractedTx1Reachability are absent. Module names alone are not object identities:
twelve formerly defective library objects have different pinned canonical
variants, one old module is absent, and two unchanged common libraries
(`FS2.DuplexDecodes`, `S2X_SecondCut`) are reused under their coherent canonical
prerequisites. Their object identities are disclosed in
NFX_LEGACY_FAMILY_PINS.json. None of the 650 old edges remains unresolved.
This is not an import of the defective original S packet forest. The scan
separately discloses 1,569 compatible cached theorem replicas; its incompatible
`duplicate_owners` counter is zero, matching the unchanged NFS scanner semantics.

The first local finalizer incorrectly banned shared module *names*. It was
replaced with exact object-variant pins, explicit old packet/owner exclusions,
and the full zero-error scan. This correction does not admit an S packet or
waive an inherited missing reference.

## Operational receipts and exclusions

All 40 host Lean/audit slots are charged. Four own input/client failures have
no normal prover receipt (L001, L013, L015, L018); L015 entered its capped launcher
but started no audit child. Failed Lean/import probes and L034's missing ten
source import baselines receive no pass credit. L035 fixes those baselines from
committed accepted sources and passes; no Lean source or binary changed for
that scan correction. L036–040 inspect complete statements and hypotheses,
including the actual headline, instead of inferring claims from names.

Own cache-order, missing-input, profiler and Python historical-view repairs
are recorded in scripts, logs and attempts. One interrupted predecessor child
regenerated an absolute-path-only report outside NFX; its exact diff is retained
and the file was restored byte-for-byte to HEAD. Subsequent child writes were
isolated. Final checks require no tracked changes outside NFX. Fresh isolated
NEI output is explicitly compared to the historical result before admission.

No timeout, memory kill, cap increase, Kani, extraction, Rust gate or ELF rebuild
occurred. No source/cfg(kani) change triggered an ELF rebuild. The caches and
wallet/account keys were retained. No push.
