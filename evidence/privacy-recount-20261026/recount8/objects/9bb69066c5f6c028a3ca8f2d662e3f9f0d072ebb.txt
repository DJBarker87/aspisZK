# Runjoin41 — source semantic payloads and opening serialization

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry `845d6424fbae0a743a9e671536606538f8c9df7a`.
Resume LOG D395. Assigned IDs 60200–60299; audit IDs 60297–60299.
**Target not yet established. Whole rows removed: 0.**

Stopped on **100-attempt Lean budget exhaustion**, with **0 Kani**.
**74 accepted / 26 rejected candidates**; all reserved audits passed.

## Obligations retained

The complete actual caller's semantic Domain remains open. The fixed layout
constructor is proved, and the actual claim_bytes output is canonical for all
caller arrays. Linking all semantic records, root, sumcheck and endpoint
output through build_with_helper_mode remains necessary.

Complete query and node opening construction, publish_compact, the security
model proof-byte equation, both native ROMView decoders, installed native
helper effects, and RustRealRefinement remain open. The op227 bridge is kept
unchanged as a named hypothesis in OracleBridge38, not used in any credited
endpoint theorem. It cannot yet be described as the sole refinement gap.

No endpoint premise or ledger row is removed. V038, V045, V163, V165, V167,
V244 and all eight PV_RunJoin_Premises fields remain: source_V045, E1_V329,
native_fill_V336, native_ledger_V337, byte_blind_V338, kernels_V339,
disclosed_V038 and observerOracle_V038. Before/after statements are byte-identical
in endpoint-boundaries-unchanged.json; fields removed/added/weakened/changed
are 0/0/0/0. TrustItems remains exactly
entropy_law, entropy_kernel, observation. Failure/divergence observations,
side channels, observer, simulator, coupling and bad/query events are unchanged.

## Checked source results

All new source modules use `R1Z.PV_RunJoin_…41`. No native or deployed closure
is inferred from an emitted-source value law.

* RowShapes41 identifies all 27 actual row shapes. LayoutArithmetic41 proves
  wrapping arithmetic by symbolic bounds. LayoutDomain41 constructs the fixed
  semantic Domain from length 13831 and 13 explicitly retained payload high-byte
  canonicality obligations. This is not the actual caller-domain theorem.
* ClaimStep41, ClaimLoop41, ClaimBytes41 and ClaimCanonical41 prove the complete
  actual claim_bytes Result: all three 29-cell point rows, then 29 extras,
  3712 bytes, and high halves zero. The universal theorem accepts actual arrays;
  no successful encoder call or byte-model equality is a premise.
* OpeningCell41, OpeningStep41, OpeningLoop41 and OpeningRow41 prove the actual
  base row (120 bytes) and secure row (32 bytes), including arbitrary wide
  values. OpeningValues41.complete proves the whole append_opening_values
  Result for every actual FibreOpening, with exact ordered 608-byte output
  and the standard explicit output-capacity bound. It does not construct or
  authenticate that FibreOpening.
* EndpointPost41 and EndpointCanonical41 prove length 928 and high-half
  canonicality on every successful actual endpoint_bytes Result, without
  assuming success. No failed/divergent Result is changed.
* PolyArrayCanonical41 specializes the existing 896-byte canonical polynomial
  law to every actual caller array. RecordFrame41 proves the actual framing
  producer's five-byte header/payload identity on success without assuming
  parser success. RecordAppend41 carries it through actual semantic_row;
  parser/transcript errors and divergence remain in the source Result.
* EncodedStep41, EncodedLoop41 and EncodedComplete41 prove the full actual
  encoded_slice Result and all 32 bytes per wide value, with an explicit
  32*length capacity domain. This supplies the four-value folded query payload
  serializer, not its construction.
* NodeTail41 proves exact zero padding within the source tail's bounds;
  NodeSlot41.source proves that this is the actual emitted node slot's tail.
  Publication indices and multiproof construction remain source calls with
  their original outcomes, not discharged helper associations.
* ArrayEntries41 relates every actual fixed array to the functional data
  representation. HighAppend41 preserves canonicality of aligned cell lists.

## Validation and process

The initial read-only preflight verifies 2559 source/object pairs, 5352 import
fingerprints, 5673 external objects and 5438 IR companions, all matching the
pinned cohort. The private runjoin32-lean workspace is retained. New launches
use only the assigned IDs, one capped scope at a time, MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000.

A premature dependent staging submission under 60213 was rejected before any
START/compiler call because OpeningStep41 had no object. Original transport,
output and reservation are retained under unlaunched-60213; the input error
was corrected and that still-unlaunched ID was used for OpeningStep41. This
cost zero additional Lean attempts. See staging-input-correction.json.

Reservation refusals at 60246, 60226, 60251 and 60297 happened before compilation
and are uncharged. Full cooldowns were observed; each still-unlaunched ID
was retained. At 60251, compile-free work prepared the record-framing target,
which used that unlaunched ID after the cooldown.


Exactly **100 single-module Lean attempts**, IDs **60200–60299**, were launched:
26 new source modules, three new focused audits and 45 inherited opening-model
prerequisites were accepted. The 26 failed candidates are retained in Git and
hash-verified by `retained-failed-sources.json`. No unchanged failed source was
rerun, no cap was raised, and no memory kill or timeout occurred. Every launch
required allowed:true and exit 0 admission. `scope-sequence-check.json` verifies
that all 100 submission/transport intervals are disjoint. The unlaunched 60213
input correction is accounted separately and is not an extra compile.

| ID | Focused audit (`R1Z.PV_RunJoin_…`) | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 60297 | CallerAudit41 | 0 | 2.34 | 4408856576 | 0 |
| 60298 | OpeningAudit41 | 0 | 1.99 | 4404867072 | 0 |
| 60299 | SourceAudit41 | 0 | 1.87 | 4405964800 | 0 |

All accepted printed axiom sets are subsets of `propext`, `Classical.choice`,
`Quot.sound`. Source statements and the retained op227 hypothesis are printed
in the audit outputs. Full commands, targets, source revisions/blobs/hashes,
dependency fingerprints, exits, wall times, RSS, swaps and axiom lines are in
`modules-*.json` and `receipt-*.json`. All 100 original module log/time pairs
are hash-verified in `original-module-logs.json.xz`. Overall peak RSS is
**4546895872 bytes**, and swaps are all zero. These are focused source audits,
not a final frozen-manifest release replay or endpoint closure.

Final read-only preflight verifies **2633 project source/object pairs**,
**5519 import fingerprints**, **5673 external objects** and **5438 IR
companions**, all matching. Lean is 4.32.0, commit
8c9756b28d64dab099da31a4c09229a9e6a2ef35. The pinned private cache is retained;
`toolchain-and-final-scopes.json` records no own running scopes. The remaining
39 staged opening-model modules without objects are listed in
`not-compiled-staged-modules.json`; their next consuming theorem is
`R1Z.ProverCommitOpeningModel53.exact_result`, then the folded opening bridge.
Those historical source/model prerequisites do not remove any ledger row.

## Release scope and next concrete deliverable

`stage-A-source-identity.json` verifies the empty crates/, programs/ and
 tools/r1-cost-probe diff from 82566acdfb; historical stage-A evidence is reused
only in its unchanged-source scope. No shipped source, key/account, other
worktree, shared source/cache or release artifact was changed. No push, merge,
extraction, Kani/native differential, ELF rebuild or unchanged full regression
was performed. The compiler-cohort, deployed ABI/features/profile, D188,
allocation/TLS/filesystem, Drop/unwind, failure-independence, K-1/K-2 and side
channel qualifications retain their prior scope. No new native credit is
claimed, and no observation has been erased to make a decoder equality hold.

The next concrete source theorem is the successful actual
`build_with_helper_mode` output's SemanticDomain40.Domain: combine the new
record framing/append laws with zero-claim and sumcheck-round accumulation,
root and final circle-record threading, then use the fixed layout constructor.
`caller-domain-obligations.json` records every offset, payload producer and
available canonicality theorem. This actual whole-caller composition is not
proved here. Next remain actual query/node opening construction,
`publish_compact`'s complete ordered proof bytes, both full native ROMView
decoders supplied to CommonSample32/CommonObserver32, installed native helper
effects, and the security-model equation/RustRealRefinement composition.

The op227 selected-callback bridge is unchanged, retains its single named
hypothesis, and is not used in any credited endpoint result. No whole row was
removed. It is not the sole remaining refinement gap.

`commits.txt` records source commits since entry; the evidence freeze commit
follows its generation.
