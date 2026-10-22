# Import-union release gate, 22 October 2026

This packet checks coexistence of the retained R22 groups, frozen2 soundness
headline, deployed privacy headline and part-52 terminal cones. It changes
instance names, not enum semantics, theorem statements or security premises.
It does not claim that the 100-bit security contract has been established.

## Source stages

- `317a687e34`: generalized adapter, deterministic migration, before/after hashes,
  and focused host checks. Forty-six files / 130 attributes changed. Default
  scope is every `docs/research/**/lean/` tree, excluding `lean-candidates`.
- `85f514f3a2`: selected retained union, raw-object preflight graphs, build plan,
  and appended session A handoff.
- `bbd9cf3985`: complete namespace overlay and preserved early cache-resolution
  failures; no theorem source repair.

`migration.json` is the first-apply before/after manifest. The check manifest
is empty; exact-byte transformation validation is in `migration-validation.json`.
Alternate files providing the same Lean module are not imported as different
modules. The retained provider selection is recorded in the rebuild plan.
Candidate sources used as unchanged dependencies are read-only; session A
receives the migration script and instructions, not edits to its candidates.

## Reproduction and cache ownership

`tools/import-union/prepare.py` selects source providers and pins the dependency
plan using the part-52 expanded terminal preflight, prior retained cone raw
object graph, and host object census. `RawObjectGraph.lean` reads actual object
headers rather than guessing repaired imports from alternate source snapshots.
All local and host caches are read-only. The private host workspace is
`/home/dombarker/project-offloads/codex-cx-import-union-20261022/`.

After preparing sources and selected `retained-objects`, run
`copy-companions.py <plan-local.json> <staging-dir>` before transferring that
staging directory to the host. This preserves `.ir`, `.olean.private`, and
`.olean.server` files required by modular Lean objects. Initialize `plan.json`
with the pinned env J and private retained-object / joint-cache paths; retain
its recorded source and object hashes. On the host, run `complete-overlay.py`
with a copy of that plan, then `sh launch-host.sh`. Do not write through any
shared-cache link: planned build outputs are excluded from linking. Lean
selects the first namespace directory, so all unchanged siblings need links
in the private overlay even when they are present later in `LEAN_PATH`.

The launcher checks the aggregate populated host reservation and runs one
sequential job in a scope with 6G high / 8G max / zero swap and 64 tasks. Every
Lean invocation uses one module, `-j1 -M7000 -DElab.async=false`, and a private
output. It stops at the first error, near 7.5 GiB sampled aggregate RSS, or ten
minutes without a compiled target. `host-build.py` reuses accepted targets by
source and direct dependency-content hashes and refuses unchanged failures.
Environment epochs identify the cache-artifact corrections below.

## Retained interruptions

- IU-10: partial private namespace directory hid cached sibling
  `AspisV8R19.SourceDuplexStep`. Complete the private namespace overlay.
- IU-11: IR companion for `Init.Prelude` was absent from that overlay. Link
  pinned host companions; IU-12 is the replacement success.
- IU-52: copied `CompPoly.Univariate.Raw.Proofs` lacked its modular server
  companion. Copy/hash all 261 selected local companions (42,187,448 bytes),
  then resume from `R1FinalSoundness` as IU-53. No memory cap was raised.

Successful predecessors were reused; none of these interruptions triggered an
unchanged full regression. The final receipt packet retains failed logs and
commands as well as their replacements. The namespace/cached-artifact repairs
change the build environment, not the formal claims.

## Terminal proof replay repair

IU-321 exposed a pre-existing simplifier boundary in
`InitialSelectorPrefix.same_boxed_success`: a concrete tuple-destructuring
`let` remained before three already-proved Result operations. A focused proof
repair explicitly changes that goal to its definitionally equal bind chain,
then uses only the existing operation equalities and `bind_tc_ok`. The theorem
statement, hypotheses, witness and arithmetic are unchanged. IU-326 passes
with standard axioms; five failed diagnostic/reduction attempts are retained
in `terminal-proof-repair/` and are excluded from accepted evidence. No failed
object was accepted and no dependent was built through a failed source.

## Final validation

Final build results, raw duplicate scan and closure validation are recorded
alongside this file after completion. `summarize-release.py` validates those
receipts without rerunning Lean. Exact per-module AGENTS fields belong in
`release-targets.json`; final aggregate fields belong in `summary.json`.
