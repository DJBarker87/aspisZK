# Runjoin40 — compact serialization source laws and retained native boundary

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry `62414c5784192f51ef49bfefa7aa99aa22892319`.
Capacity relaunch resumed the clean WIP snapshot `34518e44cb5fad141ec3e56d95ba4162661b68e4`:
97 attempts were already used; only reserved audit IDs 60197–60199 remained.
**Target not yet established. Whole rows removed: 0.**

## Requested deliverables and exact retained boundary

Neither complete deployed `disclosed` nor `observerOracle` ROMView decoder law
has been proved or supplied to CommonSample32/CommonObserver32. The installed
pv-world runtime's native helper-effect associations are not complete.
`native-decoder-gap.md` records the precise interface: RuntimeBody38 returns a
full PV_W Run including failed/divergent post-world and ordered calls, while
Deployed.Runtime's decoder fields accept an outer Result. A reachable-run
adequacy law and concrete native observer implementation remain necessary;
no failed/divergent observations have been erased to manufacture a decoder.
This is an unresolved proof obligation, not a checked shipped-source counterexample.

Commitments/openings and the complete published-proof/security-model
serialization comparison remain incomplete. RustRealRefinement is not
instantiated. OracleBridge38.selected_callback remains unchanged, with its
single named op227 selected-callback hypothesis; it is not assumed in any
credited endpoint result. V244 remains pv-b3p6f's work, and was not duplicated.
Independent byte-source work continued under the standing rule to retain an
unresolved item and proceed with other proof work.

## Checked source results

New source modules live under `docs/research/v8-r0-zk-20261009/lean/R1Z/`, with
prefix `PV_RunJoin_` and suffix `40.lean`. Every theorem has printed axioms.

* `PolyCanonical40` establishes canonical encoded polynomial high bytes.
  `PolyPublish40.encode` composes the entire actual 28-coefficient encoder
  Result with actual compact_values, proving success, exact ordered low-half
  payload and length **448 bytes** beyond the supplied output prefix. Only the
  explicit standard backend output-capacity domain remains; no successful
  codec call or zero-high-byte premise is assumed in this composed theorem.
* `SemanticCopy40`, `SemanticCompact40`, `SemanticStep40`, `SemanticLoop40`
  and `SemanticComplete40.encode` prove the complete actual compact_semantic
  successful Result and exact ordered bytes: existing output, first 32 root
  bytes, then all specified row records. Its explicit `SemanticDomain40.Domain`
  is a source byte domain: source row_shape, bounds, cursor progression,
  high-byte canonicality and terminal cursor. It contains no loop-success or
  desired model-equality premise. Establishing that domain for the actual
  caller's semantic output remains separate proof work.
* `CompactLengthReject40.reject` proves whole-buffer non-cell-aligned length
  rejection retaining the supplied output. `CompactRejectComplete40.reject`
  proves NonZeroHigh after k valid cells, with exactly their low halves
  retained, length out.length+16*k, and no bytes appended from the bad cell.
  Its source read/capacity/prefix hypotheses are explicit.
* `SemanticLengthReject40.reject` proves a semantic buffer whose length differs
  from 13831 rejects before root or row copying, preserving output exactly.
* Byte slice/read/prefix, zero-word, payload-high and length modules provide
  the named symbolic prerequisites. No large concrete recurrence was reduced.

These are complete local source Results on their stated domains, not complete
native helper associations, query/node opening construction, publish_compact,
or the final security-model proof-byte equation. Historical opening/round
prerequisites compiled here receive no row-removal credit.

## Premises and release scope

Before/after endpoint, Deployed.Runtime, CommonSample32/CommonObserver32,
observer, simulator, coupling, bad/query events, trust items and op227 bridge
are unchanged. Endpoint fields removed/added/weakened/changed: **0/0/0/0**.
V038, V045, V163, V165, V167 and V244 remain. All eight existing
PV_RunJoin_Premises fields remain. T stays exactly `entropy_law`,
`entropy_kernel`, `observation`; no missing proof was folded into T.

`stage-A-source-identity.json` records an empty crates/, programs/ and
 tools/r1-cost-probe diff from 82566acdfb. Historical stage-A evidence is reused
only in its unchanged-source scope. No shipped source, key/account, protected
soundness file, shared source/cache, other worktree or release artifact was
changed. No push, merge, extraction, Kani/native differential, ELF rebuild or
unchanged full regression was performed. D188, compiler cohort, native
ABI/features/profile, allocation/TLS/filesystem, Drop/unwind, failure
independence and K-1/K-2 qualifications retain their prior scope.

## Validation and budget stop

Exactly **100 single-module Lean attempts**, IDs **60100–60199**, were launched:
**78 accepted / 22 rejected source candidates**, **0 Kani**. Accepted results
are 22 new source modules, three focused audits and 53 inherited prerequisites.
Each launch required allowed:true plus exit 0 admission and one scope with
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000.
No cap was raised; no memory kill, timeout or unchanged failed-source rerun
occurred. All 22 rejected source blobs are hash-verified in Git via
`retained-failed-sources.json`. Own pre-admission staging/preflight argument
corrections are recorded in `staging-input-correction.json` and cost no attempt.

| ID | Focused audit (`R1Z.PV_RunJoin_…`) | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 60197 | SourceAudit40 | 0 | 1.72 | 4416131072 | 0 |
| 60198 | RuntimeAudit40 | 0 | 1.72 | 4421025792 | 0 |
| 60199 | BoundaryAudit40 | 0 | 1.66 | 4453531648 | 0 |

All printed accepted axiom sets are subsets of `propext`, `Classical.choice`,
`Quot.sound`. Full target, command, revision/blob/source hashes, dependency
fingerprints, exits, time/RSS/swap and axiom output are retained in
`modules-*.json`, `receipt-*.json` and audit output. All original 100 module
log/time pairs are hash-verified in `original-module-logs.json.xz`.
Overall peak RSS is **4527755264 bytes**; swaps are all zero. These are focused
audits, not a final frozen-manifest release replay or endpoint closure.

Final read-only preflight verifies **2559 project source/object pairs**, **5352
direct import fingerprints**, **5673 external objects**, and **5438 IR
companions**; all match. The private pinned workspace/toolchain and LEAN_PATH
are retained (Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35).
`toolchain-and-final-scopes.json` records no own running scopes. Staged opening
modules still lacking objects are named in `not-compiled-staged-modules.json`.

Stopped on **100-attempt budget exhaustion**. The next deliverable remains
full-world native runtime adequacy retaining failure/divergence observations,
then both complete decoder laws supplied to CommonSample32/CommonObserver32;
then native helper associations, commitments/openings and complete published
serialization, and finally RustRealRefinement with op227 kept as its single
named terminal gap until V244 lands. The other missing associations must be
proved before op227 can be described as the sole refinement gap.

`commits.txt` records source/evidence commits since entry; an evidence-only
freeze commit follows its generation.
