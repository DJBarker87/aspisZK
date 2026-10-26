# Resume 3: host-gated preparation

Branch `codex/pv-cb-20261026`; resume HEAD `641d98b783`.
Target not yet established. ROW-DISCHARGED(candidate): **18/73 → 18/73**.
No endpoint premise removed, no new assumption or trust item adopted.

The shared `pv-host-restored.flag` is absent at the preparation audit. Ruling
(f) prohibits **all** host scopes and local Mac Lean compiles in this resume.
No Lean/Kani/Rust/compiler invocation has occurred. The retained receipts
below are historical evidence, not a fresh dependency-closure replay.

## Budget and launch order

69 Lean attempts and 10 Kani runs remain. Assigned Lean IDs: **27100–27399**;
next unused ID **27100**. Never reuse 24000–24699, including the historical
24072 recommendation in the older resume documents. No ID has been submitted
in this resume. Read the restoration flag before any launch; its named
launcher and accepted range must be checked against this assignment.

After restoration, first inspect the existing own workspace
`/home/dombarker/project-offloads/codex-pv-cb-20261026/`. Reuse `lean-objects`
if present; otherwise populate this own workspace from restored joint objects.
Record which happened. Do not repair shared infrastructure.

First compile corrected `PV_CB_Op105Funs` (27100 if still unused), then
`PV_CB_Op105Exact`, one module per attempt. Next the existing 18-row
`PV_CB_CandidateDictionary`, five projection groups and
`PV_CB_CandidateAudit`. The audit now prints axioms for both all 18 published
source theorems and all 18 joint projections. It is not yet run.

## Prepared rows, retaining published interfaces

|op|row|status|new statement|receipt / next evidence|
|---:|---|---|---|---|
|105|V211|PREPARED, no discharge|`PV_CB_Op105Exact.op105_source`|24070 failed on shift-count type; corrected Funs numeric count remains 1, typed U32; next compile Funs then Exact|
|107|V212|PARTIAL, fresh provenance pending|`PV_CB_Op107Exact.op107_source`|`RESUME3-SIBLING-PREPARATION.json`; fresh `qm_inv` extraction, nominal field bijection, exact complete Result/Option law required|
|109|V213|PARTIAL, fresh provenance pending|`PV_CB_Op109Exact.op109_source`|same sibling evidence; fresh `wide_inv` extraction and bijective WideExact carrier required|
|118|V218|PARTIAL, fresh provenance pending|`PV_CB_Op118Exact.op118_source`|same sibling evidence; fresh `statement_points` extraction, array transport and full Result law required|

The three older `PV_CB_Op{107,109,118}Source.opN_source` statements and files
are byte-identical to resume HEAD. New Exact modules add interfaces. Emitted
names in these PREPARED modules are expected names, to be verified against
fresh `translation.json`/Funs before compilation. Their imports do not yet
exist for fresh ops 107/109/118. No compiled claim is made from them.

`PV_CB_ArrayTransport` prepares a generic symbolic list-map roundtrip for
fixed-length Aeneas arrays. `PV_CB_Op118Arrays` instantiates field/array/points
bijections. Compile the generic lemma first, then fresh Types/Funs and the
field transport, then array transport and Exact. Neither raw field values nor
array inputs are restricted; failure/divergence remain in Result.

Before starting each operation, recheck `codex/pv-cb3-20261026` for its
`opN_source`, recording the sibling revision; skip on a match. The preparation
checks found none for 107, 109 or 118. This is not a future ownership lock.

## Compile-free validation actually performed

`candidate_dictionary.py --check` passes: 18 selections, five projection
groups, and generated published-source/projection axioms audit agree with
the retained row table. This command invokes no Lean compiler.

`RESUME3-PREPARED-AUDIT.json` retains each accepted source theorem's target
receipt, exit, wall, peak RSS, swap, source revision and axioms. All 18 current
source hashes match their green receipts. Prepared files have no forbidden
proof admission or concrete `norm_num`/`decide` proof. The three published
interfaces above match resume HEAD exactly. This is source/evidence
consistency, **not** final kernel/dependency validation.

Op117 retains its exact prior timeouts and extraction obstruction. No gate
is queued unchanged, and no Kani slot has been charged. List replacement
harness names before running; stop the queue on its first configuration
failure. Native-effect deferrals remain as recorded in RESUME-SOURCE-ROWS.

Next concrete deliverable: host receipt for corrected op105 Funs, followed
by its exact current-candidate source equation. Until the flag appears,
continue compile-free work and poll its existence every ten minutes.
