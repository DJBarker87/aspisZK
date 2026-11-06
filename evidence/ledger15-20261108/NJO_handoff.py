from pathlib import Path
import json,lzma,subprocess
E=Path(__file__).resolve().parent
J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
A=J(E/'NJO_AUDIT.json');S=J(E/'NJO_SCAN.json');P=J(E/'NJO_PREDECESSOR_COMPARISON.json');X=J(E/'NJO_EXPORT.json');rs=A['resources'];seed=J(E/'NJO_CACHE_IMPORTS.json.xz');validation=J(E/'NJO_VALIDATION.json')
text=f'''# NJO ledger15 and eighth all-slices composition handoff

**Target not yet established. Full gate PASS:463 CLOSED /0 QUALIFIED /136 OPEN of599.** Branch codex/cx-ledger15-20261108; local stage commits, no push. Only NJO-prefixed modules and owned evidence directory authored. No shipped source, existing proof, trust row, sibling/session-A worktree, key or fund action.

## Exact admission

25 new occurrences, no double count: NJE TX1:118-126,128,302-304,307 and TX2:084-092,094 (24); NJB TX1:268 (1). Both transaction occurrences were independently checked against their OWN NJK obligation, source/body pin and caller clauses, even where one native certificate serves both. All original clauses retained verbatim. NJO_CANDIDATE_REVIEW.json records the exact originals and full kernel statements; NJO_HYPOTHESIS_INVENTORY.md classifies every root binder against(aq)(2). No extra endpoint/child-success/Run or arbitrary Ops assumption admitted.

Helper own domains do not close the multiproof unit.20 explicit occurrence-specific unit clauses are recorded on verify_in_place TX1:127/TX2:093, still OPEN; their basis obligations and every original caller clause are preserved. TX2's distinct proof57607/batch1/queries10..21/SAME Prepared clauses are retained.96-byte node-buffer restriction is not admitted. No driver parent or permutation/compression row promoted. NJB getter is unconditional for every typed immutable statement and preserves SAME public/transition identity; enclosing public-codec provenance remains a caller obligation.

Reviewed native cuts install SAME emitted replies with domains proved internally. Field multiplication remains Lean-discharged, never Kani. NJE/NJA native semantic controls, exact mandated KMX hash, frozen active dependency graphs, unchanged locks, offline/deployed feature selection revalidated read-only; NJB K005/K002 and frozen source identity likewise. NJG/NJA support imports earn no additional credit. Historical quarantined, timeout and incomplete packets remain excluded.

## Combined gate

L001 NJO_COMBINED_IMPORT composes NJK+NJE+NJB+NJG+NJA and AspisR1.RPx_Deployed.deployed; L002 prints all{A['required_roots']} canonical owners/full statements. All inherited row-root statements/owners unchanged. L003-L006 build the unchanged adapted NFX/raw-walker drivers with optimized links. L007 replays the SAME eight fixtures in the SAME optimized proof binary used for ALL raw groups L009-L038. L008 whole-import NFX scan exits0: {S['modules']} modules/{S['declarations']} declarations/{S['references']} references; zero dangling/incompatible or duplicate canonical owners/import mismatches. {S['compatible_cached_replicas']} compatible cache replicas disclosed under the NJK method.

All{A['required_roots']} roots audited exactly once by raw ax2; only propext/Classical.choice/Quot.sound. NHC_DecodeModel.decoder_error retains the raw-standard/empty-collect discrepancy and actual nonzero audit exit under(ab')(3), never relabelled exit0. L039 inspects positive roots and underlying cuts/source/value definitions; no new top theorem. L040 pins the entire selected closure and exports. All{P['previous_files']} predecessor files match; zero variants; {P['added_files']} added selected files. No unchanged full regression rerun.

## Physical and status

(ao)(3)(b):38/53 CLOSED,15 OPEN; (c):425/546 CLOSED,121 OPEN. TX1 shortest entry→process→stage1→stage1_owned→first_decoded→tx1 still has6 OPEN rows. TX2 entry→process→stage2→stage2_owned→tx2_authenticated→tx2_common→finish_relation has6 OPEN ancestors and a conditionally CLOSED finish endpoint. Exact row IDs/call edges/owners are recomputed in NJO_PHYSICAL.md/.json. All136 remaining rows are named in NJO_REMAINING.md with native versus Lean-only residues distinguished.

Production Pool lacks a complete authoritative numbered production inventory. NIB-P1..P4, production prefix/read/settlement, all4 held CPI/callback sites and13 exclusive-guard owners remain OPEN by name. K086 retained as liveness/abort finding; production reachability/exclusion unproved. Owner(aj)(a) PENDING. RuntimeCpiReadonlyEntry7 unused. Rulings(aq)-(au) applied; this cycle adds no ruling/trust row. PDA value row NOT added; op38 remains quantified; coherent digest/error slots op43/op44. RuntimePersistence data-only trust and seven initial Pool entry fields retain their exact scopes. P6/D188 option-A semantic transport is RECLASSIFICATION, never removal.

## Resources and restoration

40/40 serial scopes: {rs['kinds']};0 Kani/0 extraction. Every admission exit0 AND allowed:true. All6G high/8G max/swap0/tasks64, Lean-M7000;16G exception unused. Total scope wall{rs['wall_seconds']:.6f}s; maximum peakRSS{rs['peak_rss_kib']}KiB; swaps{rs['swaps']}. Exact target/argv, revision, source/dependency/Aeneas hashes, exit/wall/RSS/swap and full #print axioms retained per scope. No timeout/memory kill/cap increase.

Seed{len(seed['files'])} objects/sidecars ({seed['bytes']} bytes) copied/hash-checked read-only; zero differing seed hashes versus predecessor. Own retained export {X['export']} ({X['bytes']} bytes); prepend it to NJO_PATHS.json. No cache deleted. Source snapshots, raw reachable-constant evidence, pins and validation inputs committed; large/raw-whitespace logs compressed with uncompressed SHA256. Packaging validation PASS: {validation['source_snapshot_checks']} source snapshots, {validation['compressed_sha_checks']} compressed SHA pairs, {validation['input_pins']} input pins;12 overclaim/caller/gate mutations rejected.

Frozen crates/programs/Cargo.lock unchanged in historical-root and research scopes. No ELF rebuild trigger. Inherited pins only: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No binary/object/ELF or file over20MB committed.

Frozen3, deployed headline, L154 parameter, narrowed D188,100-bit PER-ATTEMPT soundness/privacy/two transactions unchanged. No headline hypothesis discharged. Native entry/op9/TX2 common/production Pool association, L187 cold release replay and L188 final artifact/extraction audit remain. **Target not yet established.**
'''
(E/'NJO_HANDOFF.md').write_text(text)
print('Final handoff written from checked gate, distances and resource receipts')
if (E/'NJO_HOST_END.json').exists():
 x=J(E/'NJO_HOST_END.json');p=E/'NJO_HANDOFF.md'
 p.write_text(p.read_text()+f"\nFinal retention cleanup PASS: rehashed all{x['export_hashes_verified']} retained export files before removing{sum(r['bytes']for r in x['removed'])} bytes of owned rebuildable objects/native/tmp. Cache, sources and receipts retained; no cache/key/shared path deleted.\n")
