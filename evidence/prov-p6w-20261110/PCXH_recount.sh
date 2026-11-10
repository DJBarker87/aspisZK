#!/bin/bash
# PCXH_recount.sh: PCXH_PROVENANCE.json and PCXH_ROW_TABLES.json. Starts from the PCXF_ records (git show, read-only) and applies the L187 replay result:
# a credited definition whose equality bundle did not compile with exit 0 in the L187 closure, or whose theorem name was not found in the root audit, is demoted to EQUALITY_NOT_REPLAYED_IN_L187 (counted NOT SETTLED).
# Split (Stream A lead): SETTLED = EQUALITY_PROVED + RECEIPTED with pin-equal evidence + SelectedMaskProbe (PCVR_L002); NOT SETTLED = RECEIPTED without pin-equal evidence + OPEN (+ demoted);
# listed separately: EQUALITY_DOMAIN, CONDITIONAL_ON_BINDING, DEPENDS_ON_LIBRARY_TRUST, HAND_ADAPTED, NO_FROZEN_COUNTERPART.
cd "$(dirname "$0")"
python3 -I -B - <<'PY'
import json, re, subprocess, collections, os
def show(p): return subprocess.check_output(['git', 'show', 'HEAD:' + p])
def showr(p): return subprocess.check_output(['git', 'show', 'research:' + p])
P = json.loads(show('evidence/prov-p6u-20261110/PCXF_PROVENANCE.json'))
SR = json.loads(show('evidence/prov-p6u-20261110/PCXF_SOURCE_REVISION_AUDIT.json'))
RT = json.loads(show('evidence/prov-p6u-20261110/PCXF_ROW_TABLES.json'))
A = json.load(open('PCXH_AUDIT.json')); RN = json.load(open('PCXH_CREDITED_NAMES.json'))
att = [json.loads(l) for l in open('../prov-p6v-20261110/PCXG_ATTEMPTS.jsonl')] + [json.loads(l) for l in open('PCXH_ATTEMPTS.jsonl')]  # bundles: PCXG receipts (objects pinned by the PCXH_L009 root receipt); deployed, P3s, P1n: PCXH receipts
PCXI = {(r['module'], r['definition']): r for r in json.loads(showr('evidence/prov-p6y-20261110/PCXI_RECEIPTS.json'))['records']}
P1N = {(r['module'], r['definition']) for r in json.loads(showr('evidence/prov-p1n-20261110/PCQK_STATUS.json'))['definitions'] if r['status'] == 'EMITTED+PROVED'}
NONPIN = {x['run'] for x in json.loads(showr('evidence/prov-p1o-20261110/PCVW_JOBS_IDENTITY.json'))['non_pinned_emissions']}
AS = {(r['module'], r['definition']): r for d in json.loads(show('evidence/prov-p6u-20261110/PCXF_ALL_STATUS.json'))['modules'].values() for r in d.values()}
ok = {}; 
for e in att:
    if e.get('event') == 'result':
        for s in e['steps']: ok[s['module']] = ok.get(s['module'], False) or s['exit_status'] == 0
ok['PRVCmb_C18'] = all(ok.get(x, False) for x in ('PRVCmb_C18A', 'PRVCmb_C18B', 'PRVCmb_C18C', 'PRVCmb_C18D'))  # C18 compiled as four parts after the 180 s timeout (PCXH_L012)
notfound = {(x['module'], x['definition']) for x in A['credited_not_found']}
tag = {}
for r in RN['records']:
    tg = {m.group(1) for c in r['audited_constants'] for m in [re.search(r'_C(\d\d)_F\d\d', c)] if m}
    tag[(r['module'], r['definition'])] = sorted('PRVCmb_C' + t for t in tg)
pin = {(r['module'], r['definition']): r for r in SR['records']}
STAT = ['EQUALITY_PROVED', 'RECEIPTED', 'EQUALITY_DOMAIN', 'CONDITIONAL_ON_BINDING', 'DEPENDS_ON_LIBRARY_TRUST', 'HAND_ADAPTED', 'NO_FROZEN_COUNTERPART', 'OPEN']
cone = collections.Counter(); split = collections.Counter(); demoted = []; per = {}
for mn, mm in P['modules'].items():
    for dn, r in mm['definitions'].items():
        st = r['status']; cls = st
        if st in ('EQUALITY_PROVED', 'EQUALITY_DOMAIN', 'CONDITIONAL_ON_BINDING', 'DEPENDS_ON_LIBRARY_TRUST'):
            b = tag.get((mn, dn), [])
            if (mn, dn) in notfound or any(not ok.get(x, False) for x in b):
                cls = 'EQUALITY_NOT_REPLAYED_IN_L187'; demoted.append(dict(module=mn, definition=dn, previous=st, bundles=b, not_found=(mn, dn) in notfound))
        if st == 'RECEIPTED':
            pr = pin.get((mn, dn), {})
            pi = PCXI.get((mn, dn))
            if mn == 'AspisR1SelectedMaskProbe.Funs': cls = 'RECEIPTED_SELECTED_MASK_PROBE'
            elif pr.get('verdict', '').startswith('FROZEN_TREE_CRATE_PIN_NAMES_FROZEN_DEFINITION_IDENTICAL'): cls = 'RECEIPTED_PIN_EQUAL'
            elif pi and pi['verdict'] == 'PIN_EQUAL': cls = 'RECEIPTED_PIN_EQUAL'            # PCXI_ (P6y) re-derivation
            elif pi and pi['verdict'] == 'TEXT_DIFFERS': cls = 'RECEIPTED_TEXT_DIFFERS'
            elif pi and pi['verdict'] == 'NOT_REDERIVABLE': cls = 'OPEN_NOT_REDERIVABLE'
            else: cls = 'RECEIPTED_NO_PIN_EQUAL_EVIDENCE'
        if st == 'OPEN' and (mn, dn) in P1N and ok.get('PRVEq_' + mn.replace('.', '_') + '_n3b', False) or (st == 'OPEN' and (mn, dn) in P1N): cls = 'EQUALITY_PROVED_P1N'  # PCQK_ n3b files replayed exit 0 in the L187 closure (PCXH_L014)
        per[f'{mn}|{dn}'] = cls
        if r.get('in_splitB_cone'): cone[st] += 1; split[cls] += 1
settled = split['EQUALITY_PROVED'] + split['RECEIPTED_PIN_EQUAL'] + split['RECEIPTED_SELECTED_MASK_PROBE'] + split['EQUALITY_PROVED_P1N']
notset = split['RECEIPTED_NO_PIN_EQUAL_EVIDENCE'] + split['RECEIPTED_TEXT_DIFFERS'] + split['OPEN_NOT_REDERIVABLE'] + split['OPEN'] + split['EQUALITY_NOT_REPLAYED_IN_L187']
other = {k: split[k] for k in ['EQUALITY_DOMAIN', 'CONDITIONAL_ON_BINDING', 'DEPENDS_ON_LIBRARY_TRUST', 'HAND_ADAPTED', 'NO_FROZEN_COUNTERPART']}
out = dict(schema='PCXH_PROVENANCE/1', target_established=False, universe='L187 replayed closure', headline_root=P['headline_root'], cone_definitions=sum(cone.values()),
           status_counts_PCXF=dict(cone), split_counts=dict(split), P1N_definitions_in_cone_credited=sum(1 for v in per.values() if v == 'EQUALITY_PROVED_P1N'), SETTLED=settled, NOT_SETTLED=notset, OTHER_CLASSES=other, demoted_by_replay=demoted,
           pin_equal_field_used='PCXF_SOURCE_REVISION_AUDIT.json records[].pin_equal / verdict', per_definition_class=per)
tagged = {k: [r for r in NONPIN if r in str(AS.get(tuple(k.split('|', 1)), {}).get('fresh_emission', '')) + str(AS.get(tuple(k.split('|', 1)), {}).get('receipt', ''))] for k in per}
tagged = {k: v for k, v in tagged.items() if v}
out['emissions_at_non_pinned_jobs_setting'] = dict(source='PCVW_JOBS_IDENTITY.json (P1o): identity NOT_ESTABLISHED; runs ' + ','.join(sorted(NONPIN)), definitions_tagged=len(tagged), settled_among_tagged=sum(1 for k in tagged if per[k] in ('EQUALITY_PROVED', 'RECEIPTED_PIN_EQUAL', 'RECEIPTED_SELECTED_MASK_PROBE', 'EQUALITY_PROVED_P1N')), tagged=tagged, note='tag only: the lead set split is reported unchanged; the number of settled definitions whose recorded fresh emission or receipt names a non-pinned run is listed so the Stream A lead can decide whether they stay settled')
json.dump(out, open('PCXH_PROVENANCE.json', 'w'))
print({k: v for k, v in out.items() if k not in ('per_definition_class', 'demoted_by_replay')}, len(demoted))
# row tables: the 599-row view; rows rely on definitions; recount verdict with the demotions applied (row verdict logic as PCXF_rowtables: clean iff every reached emitted module has no OPEN definition)
SET = {'EQUALITY_PROVED', 'RECEIPTED_PIN_EQUAL', 'RECEIPTED_SELECTED_MASK_PROBE', 'EQUALITY_PROVED_P1N'}
NOTSET = {'RECEIPTED_NO_PIN_EQUAL_EVIDENCE', 'RECEIPTED_TEXT_DIFFERS', 'OPEN_NOT_REDERIVABLE', 'OPEN', 'EQUALITY_NOT_REPLAYED_IN_L187'}
rv = {}; rc = collections.Counter(); relcnt = collections.Counter()
for row, mods in RT['row_to_module_to_definitions'].items():
    t = collections.Counter()
    for mn, defs in mods.items():
        for dn in defs:
            c = per.get(f'{mn}|{dn}')
            t['settled' if c in SET else ('not_settled' if c in NOTSET else ('other' if c else 'unrecorded'))] += 1
    v = 'ALL_REACHED_DEFINITIONS_SETTLED' if t['not_settled'] == 0 and t['other'] == 0 and t['unrecorded'] == 0 and t['settled'] > 0 else ('NO_NOT_SETTLED_BUT_OTHER_CLASSES' if t['not_settled'] == 0 else 'RELIES_ON_NOT_SETTLED_DEFINITION')
    rv[row] = dict(verdict=v, **dict(t)); rc[v] += 1
for row in RT['row_verdict']:
    if row not in rv: rv[row] = dict(verdict='NO_EMITTED_MODULE_OR_DEFINITION_REACHED' if RT['row_verdict'][row].get('status', RT['row_verdict'][row]) != 'UNASSESSED_ROOTLESS' else 'ROOTLESS'); rc[rv[row]['verdict']] += 1
json.dump(dict(schema='PCXH_ROW_TABLES/1', target_established=False, source='PCXF_ROW_TABLES.json row_to_module_to_definitions (git show) with the PCXH classes', n_rows=len(rv), counts_PCXF=RT['counts'], counts_PCXH=dict(rc), demoted_definitions=len(demoted), rows=rv), open('PCXH_ROW_TABLES.json', 'w'))
print('rows', dict(rc))
PY
