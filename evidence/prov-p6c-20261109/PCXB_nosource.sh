#!/bin/bash
# PCXB_nosource.sh: PCXB_NOSOURCE.json and PCXB_NOSOURCE.md for the 24 cut modules with nothing found (PCWB_CUT_TRIAGE.json), updated by later results.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6c/evidence/prov-p6c-20261109
python3 -I -B - <<'PY'
import sys, json, collections
sys.path.insert(0, '.')
import PCXB_lib as L
S = L.SCR.rsplit('/', 1)[0] + '/in'
tri = json.load(open(S + '/PCWB_CUT_TRIAGE.json'))
mods = json.load(open(L.SCR + '/compose2_modules.json')); pco = L.J('prov-p0-20261109/PCO_PARTITION.json')['modules']
nothing = [x for x in tri if x['triage'] == 'nothing']
items = []
for x in nothing:
    m = x['module']; v = mods.get(m)
    p = pco.get(m)
    if v is None:
        items.append(dict(module=m, spec=x['spec'], note='module not in the in-scope set (not reached by splitB cone or a CLOSED root, or missing from partition)')); continue
    defs = v['definitions']
    sbd = {n: r for n, r in defs.items() if r['in_splitB_cone']}
    st = lambda d: dict(collections.Counter(r['status'] for r in d.values()))
    items.append(dict(module=m, spec=x['spec'], p4b_triage='nothing', serves_CLOSED_rows=p['n_rows'], rows=p['rows'], in_splitB_cone=v['in_splitB_cone'], splitB_cone_annotated_definitions=len(sbd),
        splitB_cone_constants_reached=[n for n in json.load(open(L.SCR + '/compose1.json'))[m]['splitB_names']], splitB_definition_status=st(sbd), CLOSED_cone_definition_status=st({n: r for n, r in defs.items() if r['in_CLOSED_root_cone']}),
        rollup=v['rollup'], group=v['group'], subgroup=v['subgroup'], updated_by_later_passes='Fresh frozen emissions and P2/P5 equalities exist for part of this module (see definition_status); the missing-SOURCE finding for the hand-transformed parts is unchanged unless the module is OPEN only for reason NO_FRESH_EMISSION from cut-crate items' if sum(1 for r in defs.values() if r['status'] == 'EQUALITY_PROVED') else 'no credited equality; module OPEN',
        kani_harness='none recorded in PCWB_KANI_LINKS.json or PCWC (not searched exhaustively by this job)' if m != 'S1ValuesOwnedModelV1' else 'PCWC S3b: no Kani harness consuming the crate found',
        cost_R_reconstruct='one reconstruction of src/lib.rs from the Lean declarations plus the consuming contract, one extraction scope (about 1 s), one equality compile (about 5 s), and a NEW Kani run if a harness exists; result is a source equal in behaviour, not the original (PCWB D1)',
        cost_F_reroute=f'rewrite the bridge(s) of the {p["n_rows"]} rows to a P1 frozen emission and re-audit them; no Kani run (PCWB D1)'))
json.dump(dict(schema='PCXB_NOSOURCE/1', target_established=False, decision='NOT CHOSEN: the owner decides R or F per module (PCWB D1/D4).',
   basis='PCWB_CUT_TRIAGE.json triage == nothing (24 modules), re-read against PCXB_PROVENANCE.json definition status. P4a/P4c/P2 results do not remove any of the 24 from the list: all 24 still have no recovered Rust source for their hand-transformed definitions (S1ValuesOwnedModelV1: P4c reconstructed a source that reproduces the Funs but it is not the historical file).',
   modules=items), open('PCXB_NOSOURCE.json', 'w'), indent=1)
L_ = ['# PCXB_NOSOURCE: 24 cut modules with no recovered Rust source', '', 'Target not yet established. The owner decides reconstruct (R) or re-route (F) per module; nothing is chosen here. R/F costs are those of PCWB_DECISIONS_NEEDED D1.', '',
      '| module | rows served | in deployed_splitB cone | splitB definitions (status) | rollup | Kani |', '|---|---|---|---|---|---|']
for i in items:
    if 'serves_CLOSED_rows' in i: L_.append(f"| {i['module']} | {i['serves_CLOSED_rows']} | {'yes' if i['in_splitB_cone'] else 'no'} | {i['splitB_cone_annotated_definitions']} {i['splitB_definition_status']} | {i['rollup']} | {i['kani_harness'][:40]} |")
    else: L_.append(f"| {i['module']} | - | - | - | not in scope | - |")
L_ += ['', 'Row lists, cone constants and per-module costs are in PCXB_NOSOURCE.json.']
open('PCXB_NOSOURCE.md', 'w').write('\n'.join(L_) + '\n')
print(len(items)); print('\n'.join(L_[6:12]))
PY
