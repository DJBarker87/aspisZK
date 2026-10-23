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

The immediately dependent `ScheduleProgram.same_boxed_source_success` exposed
the same finite tuple-let boundary at IU-330. Its proof now explicitly states
the definitionally equal one-write bind chain, then uses `hwrites` and
`bind_tc_ok`; focused IU-331 passes. Statement, hypotheses and witnesses are
unchanged. Its failure and replacement are retained with the prefix repair.

The enclosing bridge next failed at IU-332. Raw-expression inspection found
that its apparent tuple `let` is Aeneas's `uncurry` combinator. The final local
lemma `uncurry_as_projections` proves its function-level projection form from
`uncurry_apply_pair`, so bind normalization works symbolically. IU-345 passes
in 1.75 s with standard axioms. Statements and hypotheses are unchanged.
IU-332–344 retain intermediate diagnostics and failed normalization attempts;
IU-334/335/338 hit the existing heartbeat guard. No limit was raised and none
of those failed proofs is accepted. The replacement avoids arithmetic
reduction and makes the helper's shape explicit.

IU-346 exposed the concrete-pair version of the same combinator in
`ScheduleCompletePacking.actual_enclosing_scheduleFamily`. Adding the pinned
`Aeneas.Std.uncurry_apply_pair` theorem to its existing `simp only` list is the
entire repair; focused IU-347 passes. No statement or witness changed.

IU-350 found the same concrete iterator-result pair in
`OccupancyLiteralLoop.loop_success_fuel`. Its base and step simplification
lists now include `uncurry_apply_pair`; focused IU-351 passes. The fuel
induction, sparse lane shape, arithmetic lemmas, statement and hypotheses are
unchanged. The recurrence was not evaluated on a generated concrete cell.

IU-353 found the symbolic and concrete forms in
`OccupancyLiteralExecutionAll12ExactListPublic`. The generated/program equality
uses the same locally proved projection lemma; the success composition uses
`uncurry_apply_pair`. Focused IU-354 passes in 5.26 s. All statements and the
12-cell model derivation remain unchanged.

IU-370 found the same iterator-result pair in the research-tree module
`AspisR1TerminalDigestBindingCandidate.LoopExact` (not `lean-candidates`). Its
two existing next-result simplifications now use `uncurry_apply_pair`;
IU-371 passed elaboration but FAILED kernel checking at the unchanged 7,000 MB memory guard (7,169,616 KiB peak RSS, zero swaps). Its earlier success wording was incorrect and is superseded here. No accepted digest-loop result is claimed from IU-371. Fuel induction and arithmetic statements are unchanged.


The digest memory obstruction is replaced by `lean/ImportUnionDigestStep.lean`.
Its `rawStep_eq_step` factors the source tweak block into the already-proved
`targetAfterLane`; `step_success` composes the existing successful primitive
calls with an arbitrary continuation. Both lemmas pass focused IU-380 with
standard axioms. The fuel theorem applies these opaque checked facts with its
actual recursive continuation; focused IU-381 passes in 2.25 s, with standard
axioms. No theorem statement or arithmetic invariant changed. The loop body
and frozen source slice remain unchanged. This permanently avoids the large
kernel conversion in the old branch proof; no cap or heartbeat increase was
used. IU-371/373/374/376/377/378 memory failures and the intervening diagnostics
are retained; they are not accepted evidence. The earlier note claiming an
IU-371 pass was erroneous and has been corrected.

IU-384 found an ambiguous `dite_true` name (`Aeneas` versus root) in
`DigestFixedBinding.false_target`. Qualifying `_root_.dite_true` is the only
change; focused IU-385 passes in 2.0 s. Statements are unchanged.

IU-407 found concrete iterator-result tuples in the outer public digest fuel
proof. Adding `uncurry_apply_pair` to its two existing next-result
simplification lists is the entire change; focused IU-408 passes in 1.75 s.
Its twenty-level symbolic induction and model theorem statements are unchanged.

The part-52 obstruction is cleared: `ExtractedDecoderCallerBridge` passes at
IU-421. Its consumer `ExtractedDecoderPublicBinding` exposed an undeclared
`PublicCodecAgreement` dependency (IU-425). The unchanged pure agreement module
passes IU-426, and adding its explicit import makes the consumer pass IU-427.
This adds the missing dependency to the plan; theorem statements are unchanged.

IU-528 found the prepared-input tuple in `AspisR1.PoseidonSamePointArray`.
Adding `uncurry_apply_pair` to its existing source-success simplification is
the only change; focused IU-529 passes in 2.51 s. The arithmetic model,
quantifiers and canonicality hypotheses are unchanged.

## Serializer cache-provider correction

The first combined import (IU-535) found `instDiscriminantErrorIsize` in the
host's cached `AspisR1PublicSerializer.Types`, conflicting with unchanged S3.
The existing canonical `lean/bridge-verify-prefix-fe80-20261017/` Types source
already names all three discriminant instances explicitly. It has no
`@[discriminant ...]` left to migrate; the problem was reuse of an older
anonymous-instance object. No historical source file is edited for this fix.

Raw provider-header snapshot IU-536 identifies a 198-module retained consumer
closure. `repin-serializer-provider.py` pins the canonical source, source
selection for its consumers, and this exact closure in `provider-repin.json`.
Types and its generated Funs pass focused IU-537/538. Existing shared objects
remain read-only; old private outputs are snapshotted on the host. The runner
records a source-hash-bound rebuild epoch for this closure, forcing its
consumers to replay even if an immediate object's bytes happen to remain
unchanged. Previously accepted targets outside that closure are reused.

This is a changed provider/dependency-input replay following a failed union,
not an unchanged full regression. The final union and raw inventory must
succeed against these corrected provider pins before this gate is accepted.

The retained generated serializer source and canonical Types have identical
carrier declarations after removing discriminant scaffolding and whitespace;
all three canonical reader code maps match the generator's default constructor
order (`serializer-provider-semantics.json`). The provider change alters no
serialized fields or tag values. During the consumer replay, the newly rebuilt
`ExtractedPublicCheckedBridge432` also required the explicit pure
`PublicCodecAgreement` import (IU-545 failure, focused IU-546 success). No
statement or hypothesis changed.

### Model alias preflight (IU-738)

Raw full modular-object census found duplicate definition owners in D18Transport/R1D18Transport, PoseidonMap/R1PoseidonMap and SpendRelation/R1SpendRelation. The first two source pairs are byte-identical. The selected old R1SpendRelation object omits AppendBinding in both Rspend and check; canonical SpendRelation retains it. New compatibility imports give each model one owner. The canonical existing R1SpendRelation wrapper is replayed with the stronger source; no security condition is removed. The raw-preflight-collisions receipt records all name/type overlaps and definition dependencies. The model-alias-repin plan forces the complete retained reverse closure, including the existing append-aware extraction source. This replay is required due to changed providers, not an unchanged regression.
