#!/bin/bash
# PCXB_final.sh: PCXB_STATUS_LINE.md, PCXB_CLASSIFICATIONS.json, PCXB_HANDOFF.md, PCXB_REPORT.md from the computed tables.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, collections
sys.path.insert(0, '.')
import PCXB_lib as L
P = json.load(open('PCXB_PROVENANCE.json')); S = P['summary']; A = json.load(open('PCXB_AUDIT.json')); R = json.load(open('PCXB_R22_SPLIT.json')); H = json.load(open('PCXB_HAND_MODELS.json'))
N = json.load(open('PCXB_NONFROZEN.json')); LL = json.load(open('PCXB_L187_RECONCILE.json'))
mods = json.load(open(L.SCR + '/compose2_modules.json')); pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
sb = S['splitB_cone']; cl = S['CLOSED_roots_union']; rows = S['rows']
orows = collections.defaultdict(set)
for m, v in mods.items():
    if v['rollup'] == 'OPEN':
        for r in pco[m]['rows']: orows[r].add(m)
opens = collections.Counter(); 
for m, v in mods.items():
    for n, r in v['definitions'].items():
        if r['in_splitB_cone'] and r['status'] == 'OPEN':
            o = r['open_reason']; opens['wrong_basis' if o.startswith('WRONG_BASIS') else 'no_fresh_emission' if 'NO_FRESH_EMISSION' in o else 'no_record' if o.startswith('no Lean equality') else 'failed_or_other'] += 1
hw = [x for x in H['entries'] if x['category'].startswith('HAND_WRITTEN')]
hw_sb = [x for x in hw if x['reached_by_splitB_cone_constant']]
sl = (f"Provenance status (P6 snapshot PCXB_, first of two P6 runs; ledger30 base 6ce07a6a593; frozen 4bb3b3f; Target not yet established). "
      f"HEADLINE CONE AspisR1.TAS_FinalB.deployed_splitB (146370 constants): {sb['modules']} emitted gate modules reached; module rollups {sb['module_rollups']}; "
      f"{sb['definitions_total']} reached annotated definitions: {sb['definitions'].get('RECEIPTED',0)} RECEIPTED, {sb['definitions'].get('EQUALITY_PROVED',0)} EQUALITY_PROVED, {sb['definitions'].get('EQUALITY_DOMAIN',0)} EQUALITY_DOMAIN (loop-return refinements only), "
      f"{sb['definitions'].get('OPEN',0)} OPEN ({opens['no_fresh_emission']} no fresh emission, {opens['wrong_basis']} wrong-basis records counted OPEN under the 2026-11-09 ruling, {opens['failed_or_other']} failed/other, {opens['no_record']} no equality record). "
      f"CLOSED-row view (599 rows): {rows.get('CONDITIONAL',0)} rows conditional at definition level, {rows.get('PROVENANCE_CLEAN_AT_DEFINITION_LEVEL',0)} clean at definition level, {rows.get('NO_EMITTED_MODULE_REACHED',0)} reach no emitted module, {rows.get('UNASSESSED_ROOTLESS',0)} rootless; "
      f"{len(orows)} rows rely on a module whose rollup is OPEN (module-level, conservative; PCO gave 565 rows relying on any non-receipted module). "
      f"Lean audit: {A['credited_theorem_names_covered']} of {A['credited_with_theorem_name']} credited theorem names audited in 11 successful scopes with only propext/Classical.choice/Quot.sound (985 PRVEq constants), one bundle scope (L006) failed and was replaced. "
      f"Hand models: {len(hw)} hand-written gate models ({len(hw_sb)} matched by a deployed_splitB cone constant), no trust row added. Not covered here: release replay, L187/L188, source-to-ELF; R22 owns checked-vs-wrapping and is not discharged by provenance.")
open('PCXB_STATUS_LINE.md', 'w').write('# PCXB status line for the next ledger\n\nTarget not yet established. The ledger job consumes PCXB_PROVENANCE.json; no ledger row was edited.\n\n' + sl + '\n\nCounts source: PCXB_PROVENANCE.json summary; deployed_splitB cone first, ledger30 CLOSED-root view for row reconciliation.\n\n```json\n' + json.dumps(dict(headline_cone=sb, closed_roots_union=cl, rows=rows, rows_relying_on_OPEN_module_module_level=len(orows), splitB_open_breakdown=dict(opens)), indent=1) + '\n```\n')
print(sl)
cls = [
 dict(id='PCXB-C1', topic='audit bundles and name collisions', classification='Credited proving files = proving_file of PROVED* PCUF_ALL_STATUS records with a correct basis (117 files, 503 definitions) plus the P4b/P4c final PRVEq files (10 files, module-level records). Files that declare a common fully-qualified name (prov-p2a NativeFunsQ415 vs p2f RPz7_FIo_NativeFuns; p2f vs p3a RPu_FIq_Native08; p2f vs p4a S8OwnedP6_Funs) go in different bundles; no renaming (renaming a gate-namespace file changes name resolution). Consequence: no single combined environment; 12 bundle scopes. Wrong-basis theorems (177 proved definitions with a basis problem) are not audited and carry no credit.'),
 dict(id='PCXB-C2', topic='scope budget and the failed shape', classification='PCXB_L006 (bundle A6, 20 files) exit 1: the S8OwnedP6 from_residual theorem of prov-p4a eq/PRVEq_S8OwnedP6_Funs.lean did not close in the bundle context (it passes alone, L011, 97 s). Shape changed: A11 = that file alone, A12 = A6 without it. L006 is retained as a failure record and not rerun unchanged. 12 Lean scopes used (L001-L012), 0 extraction, 0 Kani. The bundle-context dependence is unexplained and is a limit: that theorem is credited from the standalone scope.'),
 dict(id='PCXB-C3', topic='deployed_splitB cone walker', classification='The cone list is the ledger30-walker output NNH_L942 (146370 constants), reused and sha256-verified (0b316cbb...), not recomputed: same pinned walker binary NNM_ProofDriver 46ee271b, same root. PCWD_ReachMeta2 was not needed. The brief asked to compute with the walker; reuse of an identical-input pinned output was classified as equivalent and recorded.'),
 dict(id='PCXB-C4', topic='ownership of cone constants', classification='Same rule as PCO_partition.py stage_hits (re-run at 6ce07a6a593 reproduces module groups and row counts; one module, AspisR1WideToBytesSource.Funs, differs only by the PCO pilot/shadow correction). 209 emitted modules in the cone. Unannotated hand-written/auxiliary names reached are counted but not given a provenance status.'),
 dict(id='PCXB-C5', topic='status vocabulary', classification='EQUALITY_PROVED = PCUF PROVED_RFL/UNFOLD/EQUIV/P3 with a correct basis (P3 = nominal/source-shape transport) or a P4b/P4c audited equality with a compatible basis. EQUALITY_DOMAIN = the 4 PROVED_P3_LOOP_REFINEMENT definitions (a refinement, not a plain equality); no canonical-domain (M31.add-class) equality exists. OPEN = everything else including every record whose only basis is wrong (ruling a). TEXT_IDENTICAL_ONLY with a correct basis is OPEN. RECEIPTED = module in PCO group R (hash-linked extraction receipt); its overflow configuration is not re-derived.'),
 dict(id='PCXB-C6', topic='configuration per definition', classification='Required configuration is the PCUF value (ON unless a CONFIG_MISMATCH result showed OFF; 10 definitions). An independent text detector classifies bodies as WRAPPING/CHECKED/MIXED/NO_ARITHMETIC; 38 definitions that PCUF treats as ON carry explicit wrapping_* calls (configuration-independent: they match either emission). For P4b/P4c extras, extraction configuration was read from the PINS environment (NHV, NJT: OFF; Multiproof, archive packets: ON) and an OFF-extraction equality of a CHECKED body is counted OPEN.'),
 dict(id='PCXB-C7', topic='R22', classification='R22 (design/R22-OVERFLOW-20261021.md) owns checked-to-wrapping; its packet cites frozen source b2727acd..., not 4bb3b3f: the pin difference is noted and not reconciled here. The split is by body class; provenance does not discharge it.'),
 dict(id='PCXB-C8', topic='L187 comparison', classification='Comparison is by source sha256, not by object: L187 compared declarations (the .olean embeds the invocation path), and this job ran no object comparison. L187_SOURCE_FIXES.jsonl was read from branch codex/cx-integrate-20261107 because it was not on research when read.'),
 dict(id='PCXB-C9', topic='hand-model classification', classification='A heuristic union: explicit hand_model flags, Aeneas-generated flags and a text test (no Source: doc comment). It is a classification of campaign records, not an audit of model bodies; entries with no gate definition found are unresolved externals, not models.'),
 dict(id='PCXB-C10', topic='sibling job', classification='Sibling P1f (PCQG_) emissions and any later status were not used (none announced when this snapshot was built).'),
]
json.dump(dict(schema='PCXB_CLASSIFICATIONS/1', classifications=cls), open('PCXB_CLASSIFICATIONS.json', 'w'), indent=1)
PY
