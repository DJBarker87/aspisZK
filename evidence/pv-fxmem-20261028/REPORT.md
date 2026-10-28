# Memory callback source packages — D362 resume

**Target not yet established. No deployed endpoint premise removed.**

Worktree `/Users/dominic/ZK/.worktrees/pv-fxmem`, branch
`codex/pv-fxmem-20261028`, candidate base `10b8afe764`, resumed from `7e46a8b2c9`.
All four requested source-law packages are complete at the explicitly documented
scopes below. They are **structural (K-1 substitute)** packages, with native
checks labelled finite validation. Lead recount/acceptance remains pending;
no generic or deployed ledger row is silently marked discharged.

| Row | Exact completed package | Detail |
|---|---|---|
| V170 / op4 | Census: one call, `host_tree::multiproof_levels`, Rust `host_tree.rs:29`, emission `ProverRwFullFuns:16098`, T=`Vec<u32,Global>`. Finite-type installation, complete consumed-buffer/deallocation world law and caller composition. Other types and fields retained. | [V170](V170-RESUME.md), [census](DROP-INSTANTIATIONS.json), [gate](STRUCTURAL-DROP-GATE.json) |
| V183 / op32 | Current-world/metadata indexed original-carrier installation; complete inner Ok/Err and source error layout; values/length/capacity/pointer and allocator effects; rejection paths; caller receives the post-buffer header and world. | [V183](V183-RESUME.md), [gate](STRUCTURAL-RESERVE-GATE.json) |
| V221 / op122 | Generic element Result sequencing retains all writes in the value projection. At the actual emitted byte dictionaries: symbolic array overwrite, exact volatile-write/fence history, frame and caller laws, including consuming Zeroizing Drop. | [V221/V222](V221-V222-RESUME.md), [instances](ZEROIZE-INSTANTIATIONS.json), [gate](STRUCTURAL-ZEROIZE-GATE.json) |
| V222 / op123 | Default Result projection plus pinned literal-zero u8 Default binding; volatile overwrite, compiler fence, exact state effects and caller composition for the actual primitive dictionary. | [V221/V222](V221-V222-RESUME.md), [gate](STRUCTURAL-ZEROIZE-GATE.json) |

## Before and after

The accepted [generic finding](FINDING.md) is retained: a fixed world-free
callback cannot equal arbitrary native Drop across worlds. It is not a privacy
counterexample. V170 now has the explicitly narrower finite consumed-type law
requested by D362; the original generic assertion is not restored.

V183 is an explicitly world-indexed family, not one fixed dictionary for all
allocator worlds. V221/V222 distinguish generic value callback laws from the
physical byte law at the actual emitted primitive dictionaries. Arbitrary
custom trait effects are not inferred pure from a trait name. The exact
quantifiers, carrier identities and changed scope are in
[RESUME-ROW-STATEMENTS.json](RESUME-ROW-STATEMENTS.json).

All installations use the original carriers. `PV_FXM_AuditInstall.other_fields`
proves that restoring op4/op32/op122/op123 recovers the entire original record.
Physical allocator bytes and all accessible external state are carried inside
`Physical.Runtime`; logical allocation snapshots are explicitly distinguished
from physical freed storage. Post-reserve capacity is passed to the caller,
not reconstructed from the unchanged extracted value list.

## Verification actually run

[AuditInstall 35597](35597.json) passes. [AuditAxioms 35598](35598.json) passes all
79 retained/source-package queries, using only subsets of `propext`,
`Classical.choice`, `Quot.sound`. The one focused final
[Closure.callbacks replay 35599](35599.json) passes and queries its own axioms.
These are source/helper and packaging results, not a new composed privacy theorem.

Optimized pinned nightly-2026-06-01 native checks pass:

- `drop-u32-03`: 260 paired drop/reference cases, exact deallocation pointer/layout and counters.
- `zeroize-04`: 1,280 paired arrays and 1,280 scalar byte cases, zeros and adjacent frames checked.
- `reserve-05`: 2,160 paired cases, including injected allocation failure, overflow and ZST; complete error kind/layout, data/header and explicit call counts checked. Concrete test types include an owned Word-shaped enum; no unbounded compiler ABI theorem is inferred.
- `zeroize-drop-06`: 1,024 paired actual Zeroizing destructor cases in live MaybeUninit storage.

The retained generic finding's 32 native pairs are reused, not rerun. No Kani.
No finite validation is promoted to an unbounded memory-model or compiler proof.

[RECEIPTS.md](RECEIPTS.md) records every exact target, exit, wall time, peak RSS,
swap and revision; numbered JSON/logs include source blobs/hashes, dependency
fingerprints and full axioms. [Commit history](COMMITS-resume.txt) records the resume stages.
All new compiler/native scopes use 6G/8G/swap 0;
Lean uses -M7000. Peak Lean RSS was 2,658,476 KiB, all swap counts zero. The current
observed shared launcher and private/native scopes use TasksMax=64; legacy
35500/35501 retain their standing 128 setting. External h4 pins and the complete
project source/import resolutions are retained in the carrier preflights and
[FINAL-SOURCE-MANIFEST.json](FINAL-SOURCE-MANIFEST.json).

Budget: **31/98 resume Lean attempts**, **33/100 total**, **67 remaining**, **0 Kani**.
Rejected elaborations and two own private-environment failures remain rejected.
Refusals were uncharged. One admission retry was about 38 seconds early; admission
and caps still held. [COOLDOWN-DEVIATION.json](COOLDOWN-DEVIATION.json) records it,
and the wrapper now checks both admission stages' cooldown deadlines.

## Retained obligations and stop

The four scoped source packages, combined audit and focused replay are finished.
No privacy endpoint, observer, simulator, failure event, bound or T field was
changed. T remains exactly entropy_law, entropy_kernel, observation. No premise
was folded into T. No generic ledger flag or endpoint premise was removed.

The source laws share explicit returning raw native primitives with their owned
references. Realization of those primitives in the deployed artifact, arbitrary
OS nonreturn, the real whole-prover/RunJoin world interpreter, failure-event
witness independence, deployment E1/E2 and L1/L2/L3 remain P obligations.
The volatile source gate establishes ordered volatile writes and compiler fences
under their Rust primitive interpretation; it is not a hardware fence or an
L3 instruction/register/spill/extra-copy erasure audit. See [AUDIT.md](AUDIT.md).

Next concrete deliverable: lead recount at these exact scopes, then compose the
current-world/header-carrying source laws into the real RunJoin/deployed execution
and complete the separate L3 binary audit. No claim that privacy is established.

No crates/programs change, ELF rebuild, fresh release-pin verification, local
Lean compile, push, merge, key creation or key cleanup. Source/evidence remain;
disposable native binaries and this job's private object scratch are removed
only after their hashes and closure evidence are recorded.
