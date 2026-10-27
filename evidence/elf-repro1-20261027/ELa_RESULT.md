# Result: all three frozen ELF pins reproduced

2026-10-27; branch `codex/cx-elf-repro1-20261027` (the supplied worktree was
already on this branch). No push. Only ELa-prefixed evidence changed.

| Optimized SBF target | Exit | Wall seconds | Peak RSS KiB | Swaps | SHA-256 |
|---|---:|---:|---:|---:|---|
| default | 0 | 49.449706185 | 685776 | 0 | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 |
| devnet | 0 | 3.039015900 | 207972 | 0 | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 |
| Pool | 0 | 32.417057579 | 679972 | 0 | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 |

Sizes: default/devnet 1,563,728 bytes each; Pool 605,704 bytes. All comparisons
are byte-identical SHA-256 comparisons with the existing pins; no pin replaced.
One scope `run-r9836fa21c88f47a58b1d4e3ee0eee8c1.scope`, actual limits
6G/8G/Swap0/Tasks64, cumulative cgroup memory peak 1,398,845,440 bytes.
Each target had a 600s watchdog. No timeout/OOM, no retry or cap increase.
Reservation receipts report 32GiB then 24GiB already reserved before our 8GiB
request. Scope has ended. Budget used: **3/6 builds, 0 Lean, 0 Kani**.

## What actually ran

`ELa_build.py` replayed the retained L186 recipe against its surviving source
root read-only. Compiler-input revision `8953c28138c7e3bc31a9109e84ab3a9864090057`,
whose shipped bytes also match original S10 revision
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Default began with an empty private
Cargo target, compiling dependencies and all four selected local crates. Devnet
recompiled its program with the two retained deployment IDs, reusing unchanged
dependencies. Pool compiled Core, Statement and Pool. Exact rustc invocations,
commands/environment, source revision, caps, target, exit/time/RSS/swap and raw
log hashes are retained in `ELa_build_manifest.json` and `ELa_{default,devnet,pool}/`.
`#print axioms`: N/A, no Lean theorem or compile.

Post-build: all 1,243 source census entries and all 157 historical repository
compiler inputs match. Generated circle tables match historical
`7fbe0464c940393bf8c59e676fd60d8411a296f0260f649fa27bbf9447a96491`.
No prior ELF/object cache was used as the result. Native pinned toolchain and
Cargo's existing offline registry were reused. No Docker image was involved.
Wrapper and compiler hashes/versions match the successful L186 receipts.
Raw compiler stack-offset diagnostics are retained; these successful builds
are artifact identity evidence, not a new runtime safety claim.

## Finding disposition

`ELa_source_diff.json` compares the original pin with captured research HEAD
`66fb62bbc803f67bbeb63a786620731379d5144f`. Changed files in crates/ and programs/:
**none**. Commits since the pin touching those trees: **none**, so no changed
shipped file/commit/author lines exist to enumerate. Cargo configuration,
workspace manifest and lockfile also have no difference. No source-drift
FROZEN-IMPLEMENTATION finding is supported.

The missing original re-pin3 directory is confirmed, but does not prevent
reproduction: the surviving L186 source, identical tools and relocated private
cold target reproduce every pin. Finish-pair2's config demonstrably added
CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL=3, absent from the successful
recipe; its initial run also omitted the wrapper. This is an observed
**environment/recipe difference**, not compiler-version or shipped-source drift.
We did not run a controlled one-variable experiment assigning causality to that
single override, nor establish any timestamp/path-embedding defect. The three
successful comparisons resolve the assigned artifact reproduction gate without
requiring that stronger diagnosis.

## Obligation accounting and handoff

Before: three finish-pair2 pin comparisons failed; original historical workspace
was absent and repeatability for this follow-up was unestablished.
After: all three existing pins freshly reproduced, without shipped changes.
The theorem statement is unchanged. Ledger-method premise delta **0**; no
assumption discharged/added/changed. P7 compiler trust and existing extraction,
source/model, runtime and cryptographic boundaries remain. No ledger/contract
edits. Joint accepted non-vacuity remains separate; target not yet established.
This packet does not re-audit or close L187/L188, superseded by this artifact job.

Read-only local validation:
`python3 -B evidence/elf-repro1-20261027/ELa_verify.py` passes raw receipt/log
integrity, all three pins, common caps/scope, no source drift and current157
compiler-input hashes. See `ELa_validation.log`. Private target and diagnostic
compiled objects were removed after collecting receipts; ELF outputs and all
generated keys remain on the host, keys chmod0600. No key deleted/refunded;
no balance or authority operation performed. `ELa_cleanup.json` records cleanup.

For another authorized replay, copy committed
`evidence/lowering2-20261026/Low2_build_manifest.json` to the host job directory as
`ELa_historical.json`, plus ELa_build.py; use a fresh private output location,
check the existing reservation barrier and run the recorded systemd scope.
Do not rerun this unchanged successful build merely to repeat evidence.

Stage commits: ae7b1c94ed (recipe/source comparison), 89bc0e660f (three builds),
then this result/validation commit. No binaries, objects, archives or keys committed.
