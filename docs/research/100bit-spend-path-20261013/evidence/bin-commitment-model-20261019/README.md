# Binary commitment model evidence

Handover `61e1a7928` contained only a design skeleton and local compile tools;
there were no Lean proofs or receipts to trust or replay. Branch base is
`f9016d0a2`. Existing eight-way modules are read-only.

Compiles use the supplied local Lean 4.32 toolchain, -j1 -M4400, async off,
exclusive flock(2), and own `/tmp/r1-commit-model-20261019-objects`.
The 10 GiB free+inactive precheck is binding. Initial precheck was about
4 GiB; compilation waits rather than bypassing it.

The universal tag separation request is false: arbitrary public bytes are
hashed verbatim in verifier.rs:382. See the design obstruction.

Status and focused receipts will be appended as attempts complete.

## Handover status

**Unverified drafts, not a completed proof packet.** No Lean invocation passed
the memory precheck. There are no compile receipts, object hashes, or axiom
results to report. `manifest.json` explicitly uses nulls and draft status;
`memory-preflight.json` records the actual blocking check. No binary/object
is committed. The waiting shell was stopped; no build is left running.

25 new modules contain 106 theorem declarations. All have `#print axioms`
commands, but those commands have NOT run. Static provenance coverage, shell
syntax, Python syntax, and `git diff --check` were checked. These checks do
not establish Lean validity.

## Resume

Once the binding 10 GiB precheck is met (or the user revises it), run
`bash tools/compile_local.sh MODULE` from this worktree, in the manifest's
`compile_order`. Compile one module at a time and fix any local failures
before continuing; preserve failed receipts. The script uses the shared
flock(2) lock, -j1 -M4400, async off, and its own object directory.
No existing Lean module is edited. Do not repeat unchanged successful jobs.
The new relational multiproof semantics still needs extraction/refinement
from Rust, which is assigned to the separate source-side job.
