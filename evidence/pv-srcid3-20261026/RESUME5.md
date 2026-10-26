# Second resumed allocation

Authorized: 100 Lean compile attempts and six Kani invocations, Env-J IDs
36200–36499 (fresh IDs on every reservation refusal). Starting branch revision
34995987c0. Research snapshot is pinned in resume5-plan.json.

The original 92-entry missing inventory contains 53 sources on research and
39 unmerged branch additions. The 470-module preflight finds 85 currently
missing objects, 60 branch-only sources in the entire closure, and 66
research-source/host-source discrepancies (including absent source copies).
No merge-gate success is inferred from these checks. The research revision is
recorded explicitly rather than silently substituting the worktree revision.

Rebuilds use the unchanged shared launcher. Existing shared source and object
paths are snapshotted under this job's snapshots/resume5-ID before replacement.
Every successful rebuilt object is immediately retained in this job's own
lean-objects/R1Z directory and its exact SHA-256 recorded. This necessarily
also refreshes the shared object because the restored launcher hardcodes that
output directory; no launcher/environment infrastructure is changed. Needed
dependents are rebuilt in dependency order. Receipts pin direct imports.

36200: aggregate reservation refused (48.375 GiB + 8 GiB > 55 GiB), no Lean
scope and zero charge. Earliest retry: 2026-10-26 22:59:27.166318 UTC; fresh ID.

RunJoin's four requested published interfaces were read using git show and
pinned in resume5-runjoin-pin.json. They are not silently imported from another
worktree. InstalledTransport proves endpoint_row_call at the exact endpoint;
SelectedAdmission.Remainder retains four source families. Installation and
fixture compiler-success obligations are still explicit.

No shipped source was changed by this resume. Existing reference Rust changes
are included through the cfg(kani) proof module, as recorded by
resume5-source-boundary.json. No wallet or account keys were touched.

The first 54 named missing-object compiles pass, with standard complete printed
axioms. The initial object-retention hook was absent from the client for the
first ten completed jobs; resume5-initial-own-objects.json records their exact
outputs copied to the own object directory without any recompile. All later
successful receipts include retained_own_object directly.

The old 470-module source inventory stops at 75 external/unresolved names, some
of which are repository sources in other roots (R0P, R1, and older codec cones).
resume5-closure.py recursively resolves those project sources and records exact
object paths under the launcher's effective LEAN_PATH. It separately retains
package imports and explicitly does not claim an exhaustive package-source
replay. This distinction is part of the merge gate, not hidden by a passing
FinalAudit. The two cached extraction source variants differ in discriminant
attribute registration from research; their exact diffs are retained.
