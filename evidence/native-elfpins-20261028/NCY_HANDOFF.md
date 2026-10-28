# NCY release-route handoff — 2026-10-28

Branch `codex/cx-native-elfpins-20261028`; starting revision
`1d7752908191642fc8383c99bbadfb46fab8850c`. Local stage commits only; no push.
**Target not yet established.**

## Established, reused, proposed

Fresh optimized capped SBF builds reproduce:

- Devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
  1,563,728 bytes; exit 0, build 28.453730122 s, scope 29.39 s,
  peak process RSS 686108 KiB, cgroup peak 2506846208 bytes, swap peak 0.
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`,
  605,704 bytes; exit 0, build 29.281395283 s, scope 29.88 s,
  peak process RSS 678936 KiB, cgroup peak 2065387520 bytes, swap peak 0.

Exact scope times are authoritative in NCY_B001/B002-time.log (including any
rounding correction); exact commands/env/IDs/features/compiler invocations,
frozen source revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
payload/dependency hashes and exits/resources are in NCY_ATTEMPTS.jsonl,
receipts, compiler snapshots and NCY_PROVENANCE.json. All 1243 input hashes
match before/after both builds. Default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
is REUSED from fresh NCR_B003, not rebuilt here. No on-chain readback.

NCY_DEPLOYMENT_ROWS.md reconciles accepted L166/L176/L181/L185/headline-L187
closure with older S10 wording and states precise remaining L188 deliverables.
NCY_TRUST_INVENTORY_DRAFT.md is a SINGLE 56-row named-field/boundary table
(44 inherited field rows + 12 external/classification rows); it includes the
fifth-amendment native contract transport clarification and retained SBF
compiler semantic trust. This is a draft for L188, not a final audit or a
premise recount. Existing closed rows are reported as reused evidence.

## Assumptions and findings

Discharged here: no logical/security premise. Newly established: two requested
artifact reproductions under retained P7. Retained: all approved SDK/std,
runtime/admission/allocator/persistence/syscall, P1, narrowed D188, P6, P7 and
standard logical boundaries. No assumption added or widened. Amendment-five
uses are RECLASSIFICATION, never removal; a proposed contract is not a proof.
L154 remains a statement parameter; frozen3/two-transaction game, privacy and
100-bit PER-ATTEMPT target are unchanged.

Compiler logs contain stack-offset Error diagnostics, plus ordinary warnings,
despite successful exit and exact hashes. Dynamic symbols alone do not establish
whether those functions are linked/reachable. Retain this for S10 stack-safety
review; no proof of a deployed vulnerability or blanket stack-safety pass.
The final L188 audit must join exact RPx objects/axioms/trust, native certificate
coverage and domains, source/feature/build/ELF pins, S10 completeness and the
joint real-byte non-vacuity gate; strict import-wide F-AXIOM, W1 and body-association
qualifications remain explicit. No full manifest replay was run.

## Resources, cleanup and remaining-member accounting

Budget used: **3/6 capped scopes, 0/10 Lean, 0 Kani**. Each scope admitted only
with exit 0 AND allowed:true; one at a time, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. No cap increase, timeout, memory kill, solver rerun,
reservation refusal or shared-infrastructure repair. NCY_P001 was an own
pre-launch argument-size error, fixed by stdin transport with validation intact;
no build had started. Large compiler text transport is split per build, xz -6,
with uncompressed SHA-256 sidecars; no committed file exceeds 20 MB.

Below 80% budget completion is deliberate, member by member:

| Requested member | Why no remaining attempt is needed/authorized |
|---|---|
| Devnet reproduction | Complete bit-exact pass with pinned IDs/source/toolchain and resource receipts; another unchanged build adds no evidence. |
| Pool reproduction | Complete bit-exact pass with the pinned features/source/toolchain and resource receipts; another unchanged build adds no evidence. |
| Six deployment-row statuses | All six documented against accepted ledger/contract/replay evidence; no new theorem is needed to report status. A full manifest replay is explicitly forbidden. |
| Final trust inventory draft | Complete named-boundary draft, including amendment five and P7; final release sign-off, native bridge work and joint fixture construction are separate lead/lane obligations, not authorised by a 0-Kani status-only job. |
| Lean status checks | No new Lean module/theorem, no changed proof or missing status receipt: reused RPx_0038/0039 axioms/replay evidence suffices. Unchanged recompilation would be redundant. |

No Lean cache/object was needed; coherent SInt2 and read-only leaf caches were
untouched. No NCY Lean cache was created or deleted. I003 removed ONLY own copied
SBF target directories after builds terminated; source/diagnostics/ELFs and
all generated keypairs remain in the own host workspace, keys mode0600. No
funds/authority/key cleanup was attempted. No shipped file, existing proof,
other prefix, session A candidate/live worktree, wallet or release artifact
was edited. No binaries, keys or objects committed.

Host continuation: `/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028`.
Use NCY_PROVENANCE.json / split compiler snapshots for exact inputs; no new
build is necessary for the current pins. Next deliverable belongs to the lead:
complete L188/S10/joint-fixture review against the current accepted closure.

Static validation additionally verifies both compressed compiler transports and
reconstruction hashes, all diagnostic payload hashes, exact ELF pins, scoped
limits/admissions, retained-key modes, input checks, unchanged root-statement
SHA, and that all changes use only the assigned evidence/prefix. See
NCY_VALIDATION.json and NCY_validate.py. No file over 20 MB is committed.

Stage commits before final inventory: f3a4c9abe8 (devnet), dfff4308d3 (Pool and
provenance), af4a8742eb (deployment rows). Final inventory/handoff commit follows.
