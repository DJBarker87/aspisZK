# World interpretation — D372 resume

**Target not yet established. The requested whole-prover → existing trust
Observation theorem is not established. No new ledger row closed; no endpoint
premise or deployment condition removed.**

Exact worktree `/Users/dominic/ZK/.worktrees/pv-world`, unchanged branch
`codex/pv-world-20261028`; resume base
`95740e686418809a3ceade00cf558cd5a42cc180`. Fresh budget exhausted:
**100/100 Lean compiler starts, 0 Kani**, IDs **50400–50499** only, including
reserved audits 50497–50499. The previous stage's 100 attempts remain historical
evidence; this resume adds 100. No checked counterexample to a ROWS7 row or the
endpoint was found. The retained carrier/fixed-dictionary and new ownership
findings are not stop-rule counterexamples.

## Checked progress and its exact scope

`PV_W_R_Entry.erase_program` proves complete-Result erasure back to the frozen
`prover.prove_masked_attempt`, with the hash callback explicitly erased from
its lifted subprogram. `PV_W_R_MaskedWithAttempt.erase_program` covers the
50-call nested body, including its early rejections. The recursive translation
splices reservation/build, mask material/application, zero-factor, fixed-column,
audit, salt, opening and publishing helpers. Hash and nonce-store callbacks
are subprograms; they are not evaluated once into a fixed Result. The generator's
`--check` passes for all **26** final lifted bodies, preserving source expressions,
branches, sequencing and typed filesystem/reserve arguments.

`PV_W_ReachedThreading.entry_source`, `entry_threaded`, `entry_operational` and
`project_run` compose that concrete syntax over the enriched state/error/trace
calculus. The interpreter's `Laws` still requires local base-helper and
reserve/Drop/zeroize step validity. These are explicit **P obligations**, not
proved native purity, an installed native dictionary or new T facts. Projection
removes an internal event only under a proved OS frame law. Complete source
Result erasure is not native trace adequacy.

`PV_W_Loops` proves finite operational loop executions have an exact fuelled
state/error/trace interpretation and retain continuity, including terminal
errors and nonreturning prefixes. Its source theorem uses the pinned symbolic
`Aeneas.Std.loop.eq_def`. `PV_W_PrivateSaltsLoop` connects the actual reified salt
body to the frozen loop and proves finite source/world execution laws. This
is not a theorem of native loop termination or complete infinite traces.
The audit/inactive/opening loop bodies are independently checked. Uncompiled
fold drafts remain in Git at `d216687bb4`; they were removed from the final
accepted module set rather than presented as proved.

The exact merged fxmem sources were pinned from candidate merge `46a2203505`;
17 modules were privately recompiled. The unused aggregate `PV_FXM_Closure`
source is retained by historical citation, not loaded here. `PV_W_MemoryLift`
transports the packages' source/reference laws into the calculus at the actual
scoped types: op4 at `Vec<u32>`, world/header-indexed op32, and byte zeroize at
the emitted dictionaries. Reserve commit receives the **post-buffer/header**;
capacity/pointer are not reconstructed from element lists.
`PV_W_MemoryCombined.current_selector` uses the same combined current-world
fxmem selector for all four projections. This is source/package transport,
not realization of the raw primitives or a deployed ABI theorem.

`PV_W_ZeroizingBridge` distinguishes explicit op130 wrapper zeroization from
subsequent consuming Drop, including two actions' write/fence counts in the
package world. It does not prove L3 register/spill/extra-copy erasure or the
complete candidate dictionary installation. `PV_W_Ownership.drop_slot_once`
proves slot consumption prevents repeated glue in the ownership model; native
local-variable, move/take and scope/unwind association remains unproved.

## Missing native/Observation connection and rows

[D372-OWNERSHIP-FINDINGS.md](D372-OWNERSHIP-FINDINGS.md) identifies actual reached
`backend.c1.take()` / `c2.take()` bindings before publication scope exit. Returned
Option/Vec values alone do not encode their ownership updates or implicit Drop.
The generic Digest32/Commitments backend and its captured fields also need a
lifted interpretation; `hash : H` is not automatically the plain hash callback.
Remaining opaque helper/loop-driver leaves are explicitly listed in the
reification evidence and are not assumed natively pure.

The existing `TrustEndpoint.trustData` producer is unchanged: it copies event
fields from supplied `extractedEvents` and uses the supplied complete observer
function `extracted` as payload. This run does **not** bind those functions to
one complete interpreted prover execution, its filesystem State and its full
D159 payload. No Unit payload, reduced observer or new producer is substituted.
The replay-cache preflight qualified 560 project objects and left 270 without
qualified objects from that cache; another h6-qualified selection or private
build is required. No alternate source cohort was substituted.

New closures among V171/V172/V175/V176/V267/V268/V271: **none**.

| Rows | Remaining obligations beyond conditional threading |
| --- | --- |
| V171, V175 | Native path/flag/open/error and owned-descriptor association; complete caller/Observation installation |
| V172 | Native sync result/effect law and the distinct persistence/recovery findings below |
| V176, V268 | Complete native Error representation, payload/errno/kind decoding and required dynamic association/frame laws |
| V267 | Native partial-write/progress, Interrupted/WriteZero, retained error effects and owner/cursor/content transport |
| V271 | Native live ownership, aliasing/generation and exactly-once close/Drop across all reached exits |

Pre-existing scoped fxmem credit is reused, not recounted as new generic
V170/V183/V221/V222 closure. The privacy endpoint, bounds, adversary, simulator
(including simE), observer (including L1/L2/L3), failure event, carriers and
client/deployment conditions are unchanged. Premises removed/added/weakened:
**0/0/0**. T remains exactly **entropy_law, entropy_kernel, observation**; no
missing P fact was placed in T. E1/E2, failure-event witness independence,
whole RunJoin/native association and deployment identity remain obligations.

## OS owner findings retained explicitly

[OS-FINDINGS.md](OS-FINDINGS.md) remains authoritative here. **W-OS-1** is the
O_EXCL atomic exclusive-create/namespace obligation needed for no duplicate
successful reservation in one running namespace. **W-OS-2** distinguishes
file-data persistence from parent-directory-entry persistence and recovery;
nonce non-reuse across a crash needs the required laws for both. A source sync
call, successful reply or projected sync tag proves neither persistence law.
Neither finding is assumed, folded into observation or added as a T field.

## Validation and compact evidence

[d372-validation.json](d372-validation.json) accounts for all 100 fresh starts:
**81 accepted compilations, 19 rejected attempts**, zero Kani. Every current
new world proof source has a matching successful compile and its required
axiom queries; no unverified current world source remains. Rejected elaborations
and their sorryAx output receive no credit. The final targets are:

| ID | Exact module target | Exit | Wall | Peak RSS (KiB) | Swap |
| --- | --- | --- | --- | --- | --- |
| 50497 | R1Z/PV_FXM_AuditAxioms | 0 | 1.22 s | 2,633,904 | 0 |
| 50498 | R1Z/PV_W_D372Audit | 0 | 1.44 s | 2,642,724 | 0 |
| 50499 | R1Z/PV_W_D372Replay | 0 | 1.29 s | 2,647,100 | 0 |

All three use source revision `590c01c15c0ac3863ce763c73b16a699e3f8073b`.
Their source paths/blobs/SHA-256, dependency fingerprints, complete commands,
exit/wall/RSS/swap and full `#print axioms` output are in the numbered source
records and `lean-50497`–`lean-50499` receipts. The audits issue **79 + 89 + 7**
queries; accepted results use only subsets of `propext`, `Classical.choice`,
`Quot.sound`. This is a focused source/dependency replay, **not** a frozen
manifest/deployment release. No unchanged full regression was repeated.

Every compile used one admitted scope, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64 and Lean -M7000. Maximum observed peak RSS was
3,286,960 KiB; all swaps were zero. All 5,673 h4 external objects were freshly
hash-verified before the first compile. No external object was rebuilt or
shared source overwritten. The fxmem native/structural K-1 substitute evidence
is reused at its stated scopes; no new native differential, Rust/SBF build,
Kani gate or release-pin check is claimed.

Six reservation refusals were uncharged and retried with the same unlaunched
IDs. One retry (50434) occurred 57.47 seconds before the full cooldown;
[D372-COOLDOWN-DEVIATION.json](D372-COOLDOWN-DEVIATION.json) records the error.
The wrapper was corrected; the other five retries waited over 180 seconds,
as recorded in [d372-refusals.json](d372-refusals.json). Admission and memory
caps held throughout. Refusals were not the stopping reason.

Upload/admission inventories are represented by compact decisions and byte
hashes instead of repeated full manifests. [d372-cleanup.json](d372-cleanup.json)
retains private output-object hashes and the full host inventory's hash/path;
the **9,671,900-byte** inventory is not committed. Cleanup removed 22,637 private
object entries, zero reused targets and zero keys. Sources, receipts and
witnesses remain. [d372-source-freeze.json](d372-source-freeze.json) pins the
final checked sources and their output-object hashes. No crates/programs,
endpoint/soundness files, keys/accounts, branch, worktree or release artifact
was changed; no merge or push occurred.

History: `git log --oneline 95740e6864..HEAD`; [d372-commits.txt](d372-commits.txt)
records the implementation history through the source/audit freeze. The
previous report and receipt accounting remain in Git at `95740e6864`.

Stopped on the fresh **100-attempt budget exhaustion**. Next concrete work:
lift the generic Digest32/Commitments backend and captured fields, install the
remaining loop drivers and native ownership/move/Drop semantics, discharge the
actual filesystem/Error/descriptor leaf laws, and construct the existing
filesystem plus complete D159 Observation producer from that same execution.
The current conditional threading and source equations support this work;
they do not replace those P obligations.

Documentation correction: [D372-DOC-ERRATUM.md](D372-DOC-ERRATUM.md) corrects the
inherited transformer-name analogy; the audited Run/bind definitions and their
failure-prefix laws are unchanged.
