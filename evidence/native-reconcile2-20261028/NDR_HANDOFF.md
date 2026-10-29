# Reconciliation replay — active final-dependency checkpoint

Target not yet established. No combined replay has yet been submitted.

## Established source/theorem work

The retained FirstCaller carrier is explicit in NDO_JGi_FinishFields. NDR_L001
and NDR_B009 pass. The two release None callers explicitly use observerToFirst
none and noneToFirst, with unchanged statements: NDO_JGi_ClaimArrays in B010 and
NDO_JHm_SemanticOperands in B019 pass. NDR_ADAPTATIONS.md records exact edits,
the 23 reused replay body differences, and non-None transport limits. Arbitrary
adaptive execution transport is neither proved nor claimed.

NDR_L003 passes NDR_HeadlineNatives: fixtureInstalled, firstNative, secondNative
identify the fixture's native arguments with the headline FIp/IDa configuration
via NDO_InstalledIdentity.finalInstalled. Axioms: propext, Classical.choice,
Quot.sound only. Wall 2.839680 s; peak RSS 6,304,940 KiB; swap 0. These identify
configuration/native functions, without discharging headline trust/game premises.

NDR_L004 passes the full-name audit for all nine JHs_PDA axiom lines (the raw
`choice` spelling is Classical.choice): 2.044548 s, 5,553,944 KiB RSS, swap 0.
The offline checker requires that receipt when resolving the printer alias.

## Two isolated normal-cap import obstructions

B020 passes 37 modules then fails NDO_JHq_TX1 at plan index 2317: exit 134,
interpreter memory exception, 4.39 s module wall, 7,202,360 KiB RSS, swap 0.
Its body is a named theorem application; the import union has 13,991 modules.
Diagnostic-only L002 disables proof printing and adds a post-import marker;
it also fails before that marker (4.208081 s, 7,204,772 KiB, swap 0).
NDR_B020_OBSTRUCTION.json retains exact shape, hashes and receipts.

B027 passes 33 modules then fails NDO_JHw_Wrapper at index 3071: exit 134,
interpreter memory exception, 4.67 s, 7,170,688 KiB RSS, swap 0. The proof uses
named source applications and SDK-equality rewrites, with no arithmetic or
recurrence unfolding. Diagnostic-only L005 adds a post-import marker; it also
fails before that marker (4.015102 s, 7,171,172 KiB, swap 0).
NDR_B027_OBSTRUCTION.json records the second import union. Neither failed item
was rerun unchanged or given a larger normal cap. Diagnostic changes preserve
all theorem statements and proofs.

Exactly five normal-cap modules are failed or dependent: NDO_JHq_TX1,
NDO_JHw_Wrapper, NDO_JHw_TX2, NDO_JHw_Joint, NDO_Joint. Their bodies are reserved
for the sole final aggregation; do not credit them as standalone module builds.

## Current build state

NDR_VERIFICATION.json confirms 3,073 passing modules. Successful prefixes of
failed chunks are credited only by their own success markers, source hashes,
and axiom audits. NDR_FINAL_INDEPENDENT_PLAN.json replaces the earlier residual
plan: B028 [3072,3075) passes; B029 [3077,3117) is the CURRENT submitted scope,
40 remaining independent SHA witness modules. The serial local transport stops
at any failure. Recover submitted work read-only after interruption; never
resubmit an unchanged failed chunk or missing-receipt attempt.

NDR_BUILD_RECEIPTS.json indexes exact full receipts. Every receipt records
exit/wall/RSS/swap, limits, source revision/hash, command and axiom lines.
The full original ledger through B024 and full aggregate through B020 are .xz
with uncompressed SHA256; live JSONL indexes exact per-attempt receipts and
retains all admission records. NDR_verify_results.py is offline only.

## Pending final aggregation

NDR_CombinedAudit is PREPARED, UNCOMPILED. NDR_AGGREGATION_PACKAGING.json pins
all FIVE source bodies and the assembled source. It imports the headline and
all independently buildable prerequisites, then reproduces each blocked body's
non-import bytes verbatim in dependency order. The strict module-import variant
is preserved as NDR_STRICT_IMPORT_AUDIT.lean, uncompiled.

After B029 succeeds: run offline receipt/source/body checks; run the read-only
NDR_pin_rebuilt.py to pin successful sources/objects plus the four identity/audit
modules; commit final preflight; then ONE NDR_agg.py NDR_A001 NDR_CombinedAudit.
That script freshly verifies all three inherited lead runner hashes, requires
allowed:true AND exit 0, and uses one 14G/16G scope, swap 0, TasksMax 64,
Lean -j1 -M15000. Never rerun it after failure. Normal scopes remain 6G/8G,
-M7000, one compiler/job at a time. No extra large-cap prerequisite compile.

The final source checks both wrapper constants, original generic tree binders,
the joint runtime premise, root axioms, sourceOnHeadline through the now-proved
installed natives, all 76 historical exclusions, and the actual imported module
name array. It is a changed final aggregation source, not an unchanged retry
of either failed normal-cap module.

Even if final passes, report the exact packaging difference: FIVE modules are
not separately compiled normal-cap modules, and NDO_Joint.source is defined in
the final aggregation rather than imported from NDO_Joint. Do not claim 3,118
standalone passing module builds or a strict two-module import replay.

NDR_PROVENANCE.json records all 76 old source/object gaps as excluded from the
static retargeted graph; no historical source pin is claimed recovered. Kernel
exclusions remain pending the final source. NDR_STATEMENT_AUDIT.md retains
FixturePdaRuntime, all headline hypotheses, inherited import-wide F-AXIOM,
native/runtime/ELF limitations, and the full release contract. Root-standard
axioms do not establish import-wide standardness or the security target.

## Budget / ownership

Predecessor: 6 singles. This lane: L001–L005, total 11/60 single-module attempts.
28/40 chunks completed (26 fully pass, two failed with 70 passing-prefix modules);
B029 submitted. Combined 0/1. All admissions allowed:true AND exit 0, zero swap.
Retain /home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028; never
delete it. Predecessor caches are read-only. No wallet/key, frozen Rust, protocol,
release artifact or lead runner changed. No push or merge.
