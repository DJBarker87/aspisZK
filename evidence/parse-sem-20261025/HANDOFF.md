# Parser/semantic handoff

PARTIAL. Neither requested top gate is fully removed. S2 and the 100-bit target
remain open. Branch `codex/cx-parse-sem-20261025`; no push or merge.

## Checked source result

`PSem_Accepted.accepted_pair_claims_semantic_rows` preserves the complete
`Tx1Q_Accepted.accepted_pair_claims_tx1` statement and its SAME f,s,cuts,saved,
run and original conditional conclusions. It additionally derives
`semanticRows 27 0 (slice (bytesOf f.proof.val) 48 6983)` equal to the complete27
records returned by that TX1's actual strict Prefix parser.

No logical hypothesis is added, discharged, renamed or packed into a new
hypothesis at the accepted-pair theorem. In particular `WhenBound` still has
`parseReached` and `LiteralMatchingData.read`. Count of requested FULL top
gates removed: **0/2**. The semanticRows27 subobligation is discharged.

## Remaining work

Bind the first25 source calls, both circle calls and opening rows27..32 to ONE
33-row erased source transcript, including initialization/public serialization,
ordinary challenge carriers and source/oracle interpretation. Then prove
`Aligned` and the literal matching-data read for that transcript. `PSem_Parser`
records only the conditional composition interface; it earns no full-gate
removal credit. No checked counterexample to shipped source is claimed.

## Validation and trust

Final receipts, exact budget totals and frozen pins are indexed in the
validation summary and source manifests. This is focused checked composition
against pinned coherent caches, not a frozen-release/package replay.

## Source bodies and same-witness composition

No new installation or arbitrary successful parser slot was introduced.
The existing coherent S1 dictionary already installs the extracted
`AspisS1NativeCompact.compact.expand_semantic nativeValues` and complete owned
`expandValues` reference. The existing semantic installation calls the actual
`PrefixAdapter.parseAccepted`, source begin/finish and actual round children.
Their inherited extraction/P6/stdlib/runtime/native associations remain explicit.

New proof chain:

- `PSem_SourceCuts.{buffers,parsed_prefix}` invert this run's preparation.
- `PSem_Values.source_expansion` proves byte-exact value expansion, with its
  dimensions derived from the same complete leaf return.
- `PSem_RowStep`, `PSem_Loop` and `PSem_Expansion.source_rows` compose the
  complete native semantic expansion structurally. No concrete large-term
  replay or independently successful loop/copy/value call is assumed.
- `PSem_SourceRows.source_records` identifies every expanded row with the
  SAME strict parser's returned record, using actual lengths and partitioning.
- `PSem_FieldCanonical`, `PSem_Validation` and `PSem_Strict` transport actual
  per-limb validation and framing into the frozen semanticRows predicate.
- `PSem_SemanticRows.on_run` fixes the physical region to offset48,length6983
  of this very stored proof. The accepted-pair theorem consumes this result.
- `PSem_RunTrace.on_run` binds first25 source absorption/squeeze frames to
  those frozen rows. `PSem_SemanticTrace.verify_calls` also retains the actual
  public-transcript initialization and both subsequent circle calls.
- `PSem_Root.source_root` preserves the actual C1 root, `PSem_Y1.on_run` derives
  the physical Y1 expansion and canonical fields, and
  `PSem_ExpansionUnique.carrier_unique` derives full destination independence.

`PSem_RoundCalls` is a namespace-only port of the existing source reachability
proof with the historical heartbeat/depth overrides removed. It passes with
normal defaults. No Session A candidate or existing proved module was edited.
The first25 source-to-literal transport dependencies were built unchanged in
this worker's host directory; their generic transport hypotheses are NOT
claimed instantiated on the accepted TX1.

The bare frame equality does not establish the 33-row erased transcript,
its public statement or all challenge carriers. Downstream composition should
consume the stronger `PSem_SemanticTrace.verify_calls` initialization facts,
not infer them from a selected row list. Its existing FinishModel boundaries
remain visible. `PSem_Parser.when_aligned` shows exactly why Aligned is now the
remaining parser component, but does not prove Aligned.

## Premise audit and non-vacuity

`before-statement.lean.txt`, `after-statement.lean.txt`,
`new-conclusion.lean.txt`, `retained-when-bound.lean.txt` and `premise-audit.json`
contain the complete statements and the mechanical erasure check. Removing
only the new source-prefix/semanticRows conclusion yields the original full
statement byte-for-byte, including all binders and hypotheses. No quantifier,
carrier, failure event, security metric or assumption changes.

Retained: original SDK borrow/std/allocator/runtime/extraction/oracle, native
wrappers, ordered child marks/cuts, checkpoint/history/P2Prime and Required14
cone gates; SessionAPrepare, SessionAPrimitives including line_canonical,
domain/geometry and arithmetic owners; indexed selected-map authentication;
and the native writer's bounded admission. Most critically both requested
WhenBound gates remain. SessionAPrepare exposes only queries/rho/canonical-rho
and alpha1; it does not itself imply the whole matching-data read. No source
refinement gap is reclassified as a cryptographic assumption.

Audit099 checks inherited same-dictionary `Tx1Q_Nonvacuity` extraction
inhabitation and initial/pending success. Since this extension adds no premise
and derives its extra witnesses, it adds no contradictory admission condition.
These local checks do not establish joint satisfiability of every retained
native/runtime/cryptographic hypothesis or provide a new joint accepted fixture.
All new execution conclusions are success-conditioned. Rejection effects,
complete oracle histories and the release security experiment remain open.

## Exact validation and resource record

Budget exhausted: **100/100 Lean attempts, including33 missing unchanged
module builds; 0/40 Kani**. 71 passes,29 retained elaboration failures.
There was no memory kill, wall timeout, cap increase, unchanged failed-job
retry, Rust/SBF build or package/frozen-manifest replay.

Every attempt ran one module through the unchanged S2W host launchers with
`lake env lean -j1 -M7000 -DElab.async=false`, in its own scope with
MemoryHigh6G,MemoryMax8G,MemorySwapMax0,TasksMax64. One8GiB reservation was used
at a time. Peak observed RSS5,219,928KiB; swap0 throughout. All this worker's
jobs are terminal. Final host inventory shows two OTHER workers' scopes;
those were not stopped or modified.

| Target | Attempt | Exit | Wall seconds | Peak RSS KiB | Swap | Actual source anchor |
|---|---|---:|---:|---:|---:|---|
|PSem_SemanticRows.lean|079|0|1.918861910|5176340|0|0292113a6d + exact dirty-source SHA|
|PSem_Accepted.lean|080|0|2.212011586|5190524|0|0292113a6d + exact dirty-source SHA|
|PSem_Audit.lean|099|0|1.786719949|5159500|0|0292113a6d + exact dirty-source SHA|
|PSem_StatementAudit.lean|100|0|2.105575087|5164904|0|1f0f5e7740 + exact dirty-source SHA|

The accepted theorem's printed axioms are exactly
`[propext, Classical.choice, Quot.sound]`. Final audit099 checks all72 public
new theorems, plus the two inherited non-vacuity witnesses; only subsets of
these three axioms occur. Private helper audits are in their passing receipts.
Audit100 prints complete before/after types, WhenBound, source Call, codec
predicates, SessionAPrepare and the still-unproved read. Failed diagnostic
sorryAx output is preserved and excluded from successful proof evidence.

`validation-attempts.jsonl` records target,command,source SHA,deps fingerprint,
exit,wall,RSS,swap,axioms and actual revision anchor for EVERY attempt.
`validation-summary.json` transparently corrects inherited config revision
anchors in004 and069..080; all original receipts and exact source snapshots
are retained unchanged. Every final Lean source matches a successful receipt.
`final-host-pins.json` records66 worker-built modules' source/object/sidecar
hashes and sizes and the unchanged launcher hashes. `source-pins.json` was
rechecked against current shipped Rust. The coherent SInt2 object/source and
closure manifests are reused; no fresh coherent release rebuild is asserted.

No sorry/admit/new axiom/native_decide, heartbeat/depth override or unsafe
reducibility setting occurs in new modules. The cached-diff whitespace check
reported extra EOF blank lines in the namespace-port source, its immutable
receipt snapshot, and retained WhenBound text. Byte-exact proof sources and
receipts were preserved; these are formatting warnings, not proof failures.

No shipped file, cfg(kani) harness, feature, wire format, key/account, Session A
live worktree/candidate or release artifact changed. ELF rebuild trigger did
not fire. Inherited pins, NOT newly reproduced:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Only PSem_ modules and evidence/parse-sem-20261025 changed. No objects,
binaries,ELFs or archives are committed. All stage commits are local; no push.
