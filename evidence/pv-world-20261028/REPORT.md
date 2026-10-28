# World interpretation result

**Target not yet established. No row closed, no endpoint premise removed.**

Worktree stayed exactly `/Users/dominic/ZK/.worktrees/pv-world`. The assigned
branch `codex/pv-world-20261028` already existed at entry, at prover candidate
`10b8afe7647d478f70693d8fc12e07be871c91e0`; no branch move was necessary.
Host directory: `/home/dombarker/project-offloads/codex-pv-world-20261028/`.

## Proved and not proved

`PV_W_Threading` proves a parametric state/error/trace calculus with success,
error and divergence prefixes, pure callback lifting/frame, associativity,
ordered pre-world trace append and named `valid_emit`/`valid_bind` composition.
The generic type parameters permit an existing-World instantiation, but this
job does **not** supply the actual extracted-prover correspondence, a concrete
allocator world, a complete dictionary interpretation or an Observation producer.
In particular `valid_bind` must not be recounted as the requested caller theorem.

`PV_W_CarrierObstruction` proves no state interpreter can reproduce distinct
native outcomes whose world projections coincide. Its external-flag witness
reuses the checked FXM native normal/panic evidence, with exact git/blob/SHA
pins in reused-evidence.json. W-CARRIER-1 is a checked counterexample to a
**projection forgetting destructor-accessible state**, not to all possible
world-indexed interpretations or the actual reached destructor types. Its five
theorems have empty axiom sets. A retained-flag model proves nonvacuity.

Stopped under the checked-counterexample condition on that generic adequacy
claim. A proposed repair remains viable: enrich ordinary P interpreter state
with memory/allocator/ownership data and prove its projection to the unchanged
Observation, or prove an adequate restriction for all actual reached types.
It must also interpret source control flow before Result evaluation erases
the call sequence. This job has not established that repair.

DESIGN.md audits where threading enters today and states the sidecar design;
OS-FINDINGS.md records W-OS-1 (exclusive create) and W-OS-2 (file plus directory
crash persistence), their consequences, and their absence from existing T.
Neither is assumed. ROWS.md gives the exact remaining closure route for
V171/V172/V175/V176/V267/V268/V271/V221/V222 and effectful V170.

## Before/after and validation

Before and after: the same world-free ExternalFuns signatures and deployed
headline; T is exactly entropy_law, entropy_kernel, observation; all listed
rows OPEN. Premises removed/added/weakened: 0/0/0. No changes under crates/ or
programs/, no shared source writes, XR imports, native-decide shortcuts, key
operations, merges or pushes. No frozen extraction changes.

4/100 Lean attempts, 0 Kani. One host refusal consumed no attempt; retry
followed a cooldown exceeding 180 seconds. 36000 failed on a trace-length
elaboration (its generated sorryAx report is rejected); changed source 36001
passed. 36002 passed the obstruction. Reserved 36197 passed the combined
17-query axioms audit: only propext and Quot.sound, or no axioms. 36198–36199
are unused. All 5,673 h4 external objects were hash-verified before compilation.
No sibling project objects were loaded. Focused receipts include exact target,
revision/blob/source SHA, caps, exit, wall, RSS, swap and axiom output.
No full frozen release manifest was run: no row-closing instance was obtained.

Initial proof-driver calls before the ID preflight completed failed locally
without admission or a compiler. The broad filename scan initially matched
hexadecimal ledger/Rust fingerprints; the corrected alphanumeric-boundary
check excludes them and finds no attempt-ID collision. Both are bookkeeping
corrections, not Lean attempts. An exploratory incomplete closure lookup was
not used as source authority or as a cache-reuse certificate. Private compiled
scratch is inventoried by SHA/size before cleanup; sources/receipts are retained.

Next concrete deliverable: a sufficient P memory/allocator state and proved
Observation projection, then a syntax-directed reservation sidecar with named
open/three-writes/file-sync/directory-sync/early-error/implicit-Drop lemmas.
The complete native-world and source bindings remain proof obligations.

History: `git log --oneline 10b8afe7647d478f70693d8fc12e07be871c91e0..HEAD`;
substantive commits b2ef7df670, 98ecf596e4, 866a763184, ad2404c2b6, 273d5b9752,
followed by this evidence/receipt commit. No implementation claim is attached
to the number of commits or theorems.
