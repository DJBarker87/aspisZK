# EJR incident recovery handoff

Branch: `codex/cx-envj-rebuild-20261026`. All commits local; no push.
**Stopped at 800/800 Lean attempts, 0 Kani. S2 OPEN; target not yet established.**

## Delivered and measured

- [EJR_INVENTORY.md](EJR_INVENTORY.md), final machine inventory and exhaustive
  git-blob scan: 1,849 source-attested workspace/module entries; 1,830 resolved
  and restored byte-for-byte. Nineteen selected source hashes remain absent;
  329 historical variant hashes are absent from the local git object database.
  This does not reconstruct unrecorded disk entries or prove final historical
  source-variant coherence. Four alternative selections remain explicitly excluded.
- Integration launcher, exact committed J.json, committed run2.py, sent ledger,
  receipt/lock layout restored in the four authorized host directories. The
  highest recovered committed numeric J attempt is 23102; Stream B separately
  reports 26203. 20000–27099 are blocked as used, 28000–29999 reserved; our
  attempts are exactly 30000–30799. The quiet-window shim is retained; no
  redundant quiet-window block was added to run-joint.sh.
- 800 compiler invocations: **767 exit 0**, **33 compiler failures**.
  Complete printed-axioms gate: **765 not rejected**, **35 rejected**.
  Thirty-three project objects were reused only with matching source and
  selected dependency hashes. There are 795 original project object entries not rejected,
  plus the new smoke object; library restoration is counted separately.
- 234 exact historical library objects/companions reused. Two exact archive-pinned
  library sources were rebuilt; their object hashes differ from the historical
  pins. Intact core/package namespace directories are bound by symlinks inside
  owned output roots. Surviving caches and their sources were not modified.
- One capped scope at a time, -M7000, 6G high / 8G max / swap0 / tasks64.
  Peak RSS 7,168,572 KiB; recorded swaps 0. No cap raised. The kernel-memory
  failure was isolated and never retried. A paused coordinator's completed child
  receipt was recovered without killing or rerunning that Lean child.
- Read-only integrity check: 1,832 original/library source files, 800 compiled/reused
  object entries and 234 unchanged library objects, no hash mismatch. The smoke
  source additionally matches its committed Git bytes. J.json/launcher/run2.py
  still match their reconstruction hashes. Integrity is not a release audit.

Every attempt's exact target, command, source revision/hash, dependency hashes,
compiler/validation exits, wall/RSS/swap and full axioms/errors is under receipts/.
`lean_exit` is actual compiler status; `validation_exit` may reject a compiler
success. No .olean, IR, ELF, tarball or other binary is committed.

## Stage 5: verified launcher

`R1Z/EJR_Verification.lean`, attempt **30799**, through rebuilt run-joint.sh,
allowed reservation, exit 0; wall 0.800358 s (GNU time 0.72 s),
RSS 1,834,612 KiB, swap 0, source revision `3b597ecfa2d128b20c0302269ed3f5fd8759f499`.

```
'R1Z.EJR_Verification.successor_nonzero' depends on axioms: [propext]
'R1Z.CertSound.rinvCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The new theorem is `∀ n : Nat, Nat.succ n ≠ 0`: no antecedent and inhabited
carrier (0), so the infrastructure test is non-vacuous. It proves no security
or implementation-refinement claim.

## Standard-axiom/profile blocker

The final multiline audit corrected the initial compiler/sorryAx gate. Attempts
30628 and 30791 (J and union `AspisV8R19/SamplerWordRead`) compile but print
`core.fmt.Formatter`, inherited from the archived Fmt source's line 13 type axiom.
They are retained as excluded legacy artifacts, validation_exit=90, lean_exit=0.
See EJR_full-axioms-audit.json. The cache is **not** an approved standard-axiom
release closure. The new smoke theorem uses only propext. Selecting the
correct formatter-repair source/library profile and replaying affected consumers
requires a new budget; no post-budget proof run or silent profile rewrite occurred.

Other current blockers: EventsR1P2.card_NZ kernel memory (use symbolic subtype
cardinality/instance transport before retry), SimCostOuterRetry6 proof errors,
CertOwnFill/extracted-provider API mismatch, historical scan modules requiring
auxiliary files/IMPORT_UNION_SCAN_INPUT, and import failures that were not replayed
after namespace repair. No existing proof source was silently patched.

## Exact resume state

[EJR_resume-plan.json](EJR_resume-plan.json) lists all remaining source hashes,
1007 unattempted resolved source entries, 28 latest failed keys and nineteen
unresolved selected sources. 12 latest failures have a repaired import-context route.
Next unused attempt: **30800**. Budget remaining in this job: **zero**.

The canonical host builder is
`/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/EJR_build_host.py`.
It reuses retained objects/journals and defaults to the exhausted cumulative
limit 799. With a newly authorized additional budget N, its cumulative limit
is 800+N via EJR_CUMULATIVE_BUILD_LIMIT; do not execute this template under the
exhausted current budget. The source trees and libraries are already in place.
Repair the formatter profile and incompatible source selections before relying
on their consumer closure. Never retry EventsR1P2 unchanged. No full frozen
manifest replay or release conclusion has been established.

## Actual top theorem: before / after / recount

`AspisR1.Rc2_Top.deployed` is byte-identical before and after:
[EJR_top-before.lean.txt](EJR_top-before.lean.txt),
[EJR_top-after.lean.txt](EJR_top-after.lean.txt), SHA256
`24460608f3b6099aff4581cf34a8a3339c565a934365cf96cf480eec6e39b4fd`.
Quantifiers, carriers, failure event, conclusions and all source hypotheses
are unchanged at source level. No source hypothesis is discharged, added, renamed
or bundled. The recovered legacy formatter profile is not an approved kernel
trust closure: no top-level axioms replay or transfer across that profile is claimed.

Ledger_003–005 / Cons / Rc2 method (atomic leaves, quantified families, SAME
witnesses and shared-dictionary deduplication), using unchanged Rc2_premises.json:

| Scope | Before T/P/C | After T/P/C | Delta |
|---|---|---|---|
| actual application conditions | 82 / 171 / 0 | 82 / 171 / 0 | 0 / 0 / 0 |
| deduplicated actual + non-alias deployment | 88 / 184 / 0 | 88 / 184 / 0 | 0 / 0 / 0 |

This is a static zero-delta recount against identical source, not a fresh top
replay. No security-theorem non-vacuity witness was added or re-established.
Infrastructure recovery removes **zero actual top premises**. S2 remains open.

No shipped file or cfg(kani) module changed; no ELF rebuild trigger fired.
Inherited, not newly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Session A worktrees/candidates and other live workspaces were not modified.

## Commits before this final receipt commit

```
3b597ecfa2 Rebuild env J objects within the recovery budget
3d1e4d3482 Resolve remaining source blobs and stage pinned library recovery
ccf5545952 Recover additional source attestations from launcher output arrays
d6dd1ca963 Restore hash-resolved env J and import union sources
e2d2868c32 Restore env J launcher environment and attempt ledger
06c589dcd4 Inventory recoverable env J source provenance
```
