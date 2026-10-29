# D518 resume: translator identity recovered; client translation still gated

Branch `codex/pv-cx-20261029`, exact worktree
`/Users/dominic/ZK/.worktrees/pv-cx`; resume head
`570c0008098b8cc23d16d86f9edb0c2a41b0e118`. All 1,225 staged frozen inputs still
match the accepted N73309 source pins (`current-frozen-source-check.json`).
No crates/programs/tools/r1-cost-probe file changed. The privacy target is not
established. **Rows removed: NONE.** No privacy premise is discharged, added,
weakened or reclassified; the same 19 runtime fields remain OPEN.

## Delivered: ae1 translator identity

`translator-identity.json` records the accepted translator as
**functionally identical rebuild (ae1-2)**. Fresh upstream b59d5188 checkout,
plus the retained `accepted-extensions.patch` (SHA 3b9d03d6...), matches all 776
regular files in the original source manifest. `source-recovery.json` records
each comparison. The aggregate patch and original archived extension patch,
their difference, and retained OCaml/opam manifests are committed here. No
existing Aeneas source or executable was overwritten.

New host directory: `/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/`.
N73330 rebuilt statically in the pinned Docker image with OCaml 5.2.1,
dune 3.24.2, the retained opam packages, release profile and four jobs. Binary:
`aeneas/src/_build/default/main.exe`, 49,422,424 bytes, SHA-256
`fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68`.
It differs from historical 4632746d; exact binary identity is NOT claimed.
The original 4632746d build's complete package lock was not independently
recovered: the retained opam lock is from the later source-preserving rebuild;
the older static-build log records Nix OCaml 5.2.1/dune 3.20.2. These records
are distinguished in the identity artifact rather than conflated.

Mandatory functional comparisons all pass, with original LLBC input hashes,
flags, generation audits and every Lean output comparison recorded:

- N73331: caller-005 (the ProverRwFull generation input), all four Lean files.
- N73332: prover-attempt-064, all four Lean files.
- N73337: sampler-001, Types and Funs.

The tracked `stage3/adapt-caller.py` was then replayed with ONLY I/O path
constants redirected. All four resulting ProverRwFull files, including Types
and Funs, byte-equal both the historical adapter manifest and the files at
resume HEAD. This is an identity test only: no regenerated prover is installed
in the new client or substituted for an existing Lean declaration.

The 562e1f51 backup fails the necessary caller-005 comparison (N73334, exit 2):
`ProverRwRngExtractor006: fail-closed preflight: escaping reference output requires
loan validation; structured Drop requires destructor semantics`. It is rejected
and never used for client translation. The other two backup comparisons are
unnecessary after this failure and were not run. A later attempt to launch one
was refused before execution.

## Client translation attempts

N73338 ran the accepted rebuild on the EXACT N73309 LLBC. Aeneas exits 2:
`Nested-loop returns require exactly one Option language item`, at
`src/bin/devnet_spend/plan.rs:25:0–25:407` (`note`). N73309 contains 12 Option
language items (`N73309-option-shape.json`). The recorded prepass is unconditional
and constructs a generic Option carrying the return value. No CLI flag disables
it. `PrePasses.ml.excerpts.txt` and its full-file hash preserve this check.

Flag/opacity-only alternatives preserve main/run/prove and the frozen source:
N73339 removed monomorphization and attempted to opaque Accounts::parse;
it timed out at 540 seconds after rebuilding dependencies. N73340 corrects
that inherent-impl matcher to `_::parse` and reuses the compiled dependencies:
Charon exits 0, but `has_errors=true`, with 38 wincode associated-type lifting
warnings at `devnet_spend.rs:21:8` and `wincode/schema/tag_encoding.rs:138:5`.
N73341 adds no-normalize (NOT no-typecheck): 76 warnings, still rejected.
N73342 instead removes unused clauses: Charon panics in
`remove_unused_clauses.rs:133` with `mismatch while trying to remove unused clauses`.
No erroneous LLBC is fed to Aeneas.

N73343 expands the Aeneas preset into its ten non-lifting flags and lifts only
the seven reached trait roots other than wincode. Charon has_errors=false;
main/run/prove are still structured and only Accounts::parse is newly opaque.
The raw text and compressed artifact are retained and hashed in
`alternative-llbc-manifest.json`. But N73344 exits 1: pinned Aeneas unconditionally
requires serialized `preset=Aeneas` metadata. Charon's Aeneas preset necessarily
adds blanket associated-type lifting. Neither metadata editing nor modifying
the extractor is authorized; neither was done.

N73345 was refused before launch. After cooldown, N73346 restores the accepted
monomorphized Aeneas preset and marks only note and Accounts::parse opaque.
It has has_errors=false; main/run/prove remain structured. N73347 then fails
at the REQUIRED body `plan::prove`, `plan.rs:80:0–130:1`, with the same
`Nested-loop returns require exactly one Option language item` refusal.
This isolates the obstruction beyond optional helpers: the loop at line 92
contains fallible calls returning through `?`. Making prove opaque would remove
the executable path explicitly required by the task.

**Stopped item:** no accepted flag/opacity-only route was found. The paired
mandatory preset/lifting checks and monomorphized generic-Option prepass reject
the tested frozen-source paths. Continuing by editing LLBC preset metadata,
rewriting the loop, changing the translator, or replacing the body with a port
would exceed this task's authorization. This is the owner/lead deliverable:
authorized compatible handling of this mandatory source construct by the pinned
extraction chain, with source-fidelity and translator-identity gates retained.
The successful translator restoration itself does not require an owner waiver.
No Types/Funs compilation, standard-axioms audit, manifest replay, or compiled
prover declaration-identity link is claimed. No replacement prover or world was
written. Existing V370, V371, rdea-1, V400/V396, D159/D166, and L1/L2/L3/source/
experiment obligations are retained; no T field or observer/simulator changed.

## Delivered: 62 source-role classifications

`effect-interface.json` resolves every previously empty category, preserving
all 436 opaque IDs/signatures and all static sites. Each of the 62 changed rows
includes definition-file SHA, complete definition excerpt, call sites and
contextual reasoning. The 18 application files match baseline git blobs;
external definition source versions match those named by the accepted LLBC.
No 1.94.1 standard-library law is inferred from a nightly definition.

The classification is operation-role evidence, NOT an effect-freedom theorem.
Allocation, panic, hashing/callee, backtrace/environment and drop adequacy remain
explicit. The six opaque constant initializers have no static call sites.
`EFFECT-CLASSIFICATION.md` also identifies a bug in the old classifier's generic
name substring matching for clock labels. The other 374 inherited labels stay
marked unverified; this audit does not claim a complete transitive effect law.

## Resource/admission and validation

Every executed scope has 6 GiB high / 8 GiB max / swap 0 / 64 tasks, with both
admission exit 0 and allowed:true before creation and at the release barrier.
All run receipts record target, exit, wall, RSS, cgroup peak, swaps, source
revision and N/A axioms status. No memory kill occurred. N73339's GNU-time RSS
covers the timeout wrapper and undercounts descendants; use its full cgroup
peak (3,371,724,800 bytes) for resource accounting. No cap/timeout was raised.

N73333 and N73335 were refused before execution; their next actual launches
followed the full 180-second cooldown. N73345 was also refused; N73346 followed its full cooldown. Refusals are uncharged.
Python scripts parse and identity/source/site preservation checks pass.
`validation.json` lists actual executions; no unexecuted Lean ID is counted.
No key/account was created, used, removed or deleted. Nothing was pushed.


Final usage: **14/20 native scopes, 0/40 Lean, 0 Kani**. Refused/unlaunched:
N73333, N73335, N73345 (uncharged). Native executions:
N73330–73332, N73334, N73337–73344, N73346–73347.
All Lean IDs remain unused, including the audit reserve. This is a checked
mandatory-source extraction refusal, not budget exhaustion. There is no
new Lean statement to elaborate or theorem closure to audit. The task-specific
ban on source ports/references and extractor changes prevents the inherited
generic P6 fallback from bypassing this refusal. h6/h6'/h6'' object
reconciliation was not exercised: no new Lean import closure was loaded.

Cleanup preserves the accepted 49,422,424-byte translator under the new host
resume directory's `pinned-tools/aeneas-ae1-2-fda587d2`; hash unchanged.
Only this resume's Rust/OCaml compiled scratch was removed, after checking all
owned native scopes are inactive. Sources, raw/compressed LLBC, receipts and
other jobs' caches/tools are retained. `cleanup.json` records exact paths.

Stage commits from resume HEAD are recorded in `commits.txt` (the final evidence
commit may follow that snapshot). No push or branch change occurred.
