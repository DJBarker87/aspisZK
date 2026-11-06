# NJP handoff

Target not established. TX1:306 and TX1:305 have locally gated CLOSED candidate
packets. TX1:127 and TX2:093 remain OPEN. No authoritative ledger change or push.
Only NJP-prefixed evidence/modules were changed; no sibling/session-A worktree
was modified. Frozen crates/, programs/ and Cargo.lock remain byte-identical.

## Candidate packets

Read NJP_CLOSED.json, NJP_ROW_PACKETS.json, NJP_ROOT_STATEMENTS.md and
NJP_LEDGER_DELTA.json. The baseline is ledger14's NJK_LEDGER, not running
ledger15. Lead credit must wait for the next ledger gate, including NJE's callee
candidates. The roots are NJP_PermutationPacket.TX1_306 and
NJP_CompressionPacket.TX1_305. These are direct P6 hybrid packets under recorded
own domains, with child models substituted at SAME arguments. Native semantic
transport is P6/D188 option-A reclassification; no trust item was removed/added.

306: K006/K007 bind the 22 actual round/kind descriptors; K008/K009 establish
noop-callback rename stability. NJP_ControllerTrace threads NJE's round
witnesses, including canonicality and final fold. Arithmetic bodies in this
controller gate are control-only records, not field-value credit.
305: K057/K058/K059 refresh exact KMX slice-copy coverage and prove SAME complete
seeded state and SAME first-eight returned limbs, including readonly inputs.
NJP_CompressionPacket installs the permutation candidate at that exact seed.

## Shared verifier work

K013–K073 provide full-range windows, separate occupied/supplied branches,
real write windows, full frames, outer/entry/terminal control, pending sibling
prefix and scalar cuts with semantic controls. K023 is a timeout with no credit;
the replacement uses split windows instead of its duplicate payload product.
NJP_NATIVE_SUMMARY.json gives all 70 native outcomes: 33 positives, 35 semantic
negative controls, one setup failure, one timeout. No multiplication in Kani,
no new copy stub, no Option<fn>-dependent credit, no function contracts.

NJP_NativeCohortStep.observation, NJP_CohortNode.observation,
NJP_CohortRowLoop.rows, NJP_CohortHeightLoop.levels,
NJP_CohortReturning.observation and NJP_CohortTotal.levels compile. They carry
complete Result, both full buffers, cursor and chronological request/reply log.
The totality bound is 9216 bytes; no <=5504 strengthening was introduced.
NJP_CohortTerminal.same checks all terminal clauses without acceptance premises.
NJP_AbortTransport.abort_prefix retains the unanswered pending request.
These are shared support roots, not complete verifier-row certificates.

NJP_REMAINING.md lists both verifier obligations separately. L076's
NJP_VerifierView is UNCOMPILED (namespace/guard elaboration), excluded from the
combined import/export/axiom root set. Its historical failed output may contain
diagnostic sorryAx and has no credit. Native entry/wrapper association, exact
adopted endpoints, all caller unit-domain clauses and complete native abort
prefix attachment still need their final TX1/TX2 packets. Lean-only work remains;
the stopping reason is the exhausted Lean budget, not Kani exhaustion.

## Audit and resources

Exactly 70/70 Kani and 80/80 Lean/link/audit scopes, zero extraction. Every
attempt has its configuration, admission, frozen dependency/unchanged-lock
validation where applicable, source/revision pins and resource receipt.
NJP_RESOURCE_SUMMARY.json indexes target, exit, wall time, peak RSS and swap;
receipts also contain limits, source and selected Aeneas-object hashes.
CARGO_TARGET_DIR was always the owned workspace's NJP_target. Host scope caps
were MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Lean used -M7000;
no cap/timeout increase or unchanged timeout/memory-kill rerun.

Both allowed combined audits passed. Final L078 imports NJK_COMBINED_IMPORT,
NJE_COMBINED_IMPORT and 33 own modules with AspisR1.RPx_Deployed.deployed.
L079's NFX scan: exit 0, 15,474 modules, zero dangling/duplicate/import defects,
36.0735s, peak 7,390,924 KiB, swap 0. L080 raw ax2: exit 0, 102 roots,
22.0718s, peak 6,784,324 KiB, swap 0; raw walk equals collectAxioms for every
root and only propext/Classical.choice/Quot.sound occur. Every new accepted top
theorem has #print axioms. L024's eight fixtures/mutations remain valid for the
unchanged driver algorithm. See NJP_AUDIT.json and NJP_RAW_RESULTS_GATE2.json.
No third full audit or release manifest replay was run.

## Retained host export and cleanup

Workspace: /home/dombarker/project-offloads/codex-cx-multiproof3-20261108
Retained export:
/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJP_20261108/NJP_exports_20261108

Seeded by copying NJE's retained export first: 43 files, 7,347,304 bytes;
NJP_SEED.json records imported hashes. Final own export: 36 compiled files,
6,882,584 bytes; NJP_EXPORT.json pins every retained object and the 3,119 owned
build artifacts before cleanup. Use this export before any new build, together
with the pinned coherent dependency paths in NJP_ENV_COMBINED.json and receipts.
Own seed/cache were retained. After hash-verified export, only own rebuildable
NJP_target, NJP_objects and the two audit executables were removed; native C,
scratch sources and receipts remain. Host free space increased from
10,653,093,888 to 15,031,365,632 bytes. No wallet/account key was created,
deleted or otherwise touched.

No shipped-file change triggered ELF rebuilds. Inherited ELF identities remain
recorded in NJP_SHIPPED_IDENTITY_FINAL.json and NJP_RELEASE_PINS_REFERENCE.json;
this run does not claim new ELF measurements. The headline remains deployed,
frozen3 and the approved two-transaction model with L154 a statement parameter
and narrowed D188. RuntimeCpiReadonlyEntry7 was not used.
