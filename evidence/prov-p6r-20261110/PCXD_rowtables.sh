#!/bin/bash
# PCXD_rowtables.sh: PCXD_ROW_TABLES.json = the row-to-module and row-to-definition tables behind the 599-row view (the PCXB_ run kept them in scratch).
# Method (a stranger can rerun this):
#  1. Roots. roots.json maps each of the 1099 ledger30 root constants to the CLOSED ledger rows it serves (ledger30 NNN_LEDGER.json.xz, status CLOSED; 599 rows).
#  2. Reach lists. For every root, its pinned REACHABLE constant list (ledger29/ledger30 NEP proof0 REACHABLE.txt.xz, hash-pinned, 6ce07a6a593 tree) is intersected with the
#     'strong_names' of each emitted gate module (emods_decl.json, PCO_partition.py stage_hits ownership rule: strong_names per module, private-name handling, longest-prefix
#     fallback) giving emod_hits.json: root -> module -> constant names. (PCXD_reach.sh does the same for the headline TAS_FinalB.deployed_splitB list, 146370 constants.)
#  3. Row tables. closed_rows = invert(emod_hits o roots): module -> row -> definition names reached (PCXD_compose1.sh; reproduced byte-identically from the PCXB_ table).
#  4. Row verdict (PCXD_compose2.sh): a row is PROVENANCE_CLEAN_AT_DEFINITION_LEVEL iff it reaches >= 1 emitted module and every annotated definition it reaches has status RECEIPTED, EQUALITY_PROVED or EQUALITY_DOMAIN;
#     CONDITIONAL if some reached definition is OPEN / HAND_ADAPTED / NO_FROZEN_COUNTERPART / CONDITIONAL_ON_BINDING; NO_EMITTED_MODULE_REACHED; UNASSESSED_ROOTLESS.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6r/evidence/prov-p6r-20261110
python3 -I -B - <<'PY'
import sys, json, collections, hashlib
sys.path.insert(0, '.')
import PCXD_lib as L
S = L.SCR
roots = json.load(open(S + '/roots.json')); hits = json.load(open(S + '/emod_hits.json')); closed = json.load(open(S + '/closed_rows.json'))
rows = json.load(open(S + '/compose2_rows.json')); sb = json.load(open('PCXD_SPLITB_HITS.json'))
mods = json.load(open(S + '/compose2_modules.json'))
row_to_mod = collections.defaultdict(dict)
for m, d in closed.items():
    for r, ns in d.items(): row_to_mod[r][m] = ns
# row -> module -> {definition: status} for the annotated definitions only (the definition table the verdict uses)
row_defs = {}
for r, d in row_to_mod.items():
    row_defs[r] = {m: {n: mods[m]['definitions'][n]['status'] for n in ns if n in mods[m]['definitions']} for m, ns in d.items()}
mod_status = {m: dict(rollup=v['rollup'], group=v['group'], counts=v['counts']) for m, v in mods.items()}
out = dict(schema='PCXD_ROW_TABLES/1', target_established=False,
  method='see the header of PCXD_rowtables.sh (also reproduced in PCXD_REPORT.md section 6)',
  inputs=dict(ledger='ledger30-20261111/NNN_LEDGER.json.xz (CLOSED rows)', partition='prov-p0-20261109/PCO_PARTITION.json', status='prov-p2j-20261110/PCUJ_ALL_STATUS.json + PCXD overlays (PCXD_PROVENANCE.json)',
               splitB_list='integrate-20261111/NNH_L942 REACHABLE list (sha256 0b316cbba462874e984430db4c9ddcaa2d902053315934a8b608eaea48d30090)'),
  counts=dict(roots=len(roots), roots_with_hits=len(hits), modules_in_scope=len(mods), closed_rows_in_table=len(row_to_mod), rows_total=len(rows), verdicts=dict(collections.Counter(v['status'] for v in rows.values()))),
  root_to_rows=roots, row_verdict=rows, row_to_module_to_definitions=row_defs, row_to_module_to_reached_names=row_to_mod, root_to_module_to_reached_names=hits,
  splitB_module_to_reached_names=sb['modules'], module_rollup=mod_status)
raw = json.dumps(out, separators=(',', ':'))
open('PCXD_ROW_TABLES.json', 'w').write(raw)
print(len(raw) / 1e6, 'MB', out['counts'])
PY
