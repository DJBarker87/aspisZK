#!/usr/bin/env python3
"""PCO_partition_delta.py: compare a recomputed partition with PRV_PARTITION.json and attribute each change.
Usage: PCO_partition_delta.py OLD(PRV_PARTITION.json) NEW(PCO_PARTITION.json) OLD_SCRATCH NEW_SCRATCH OUT.json
OLD_SCRATCH/NEW_SCRATCH are the PCO_partition.py scratch dirs (fresh_files.json, ledger rows) used for the attribution."""
import json, sys, collections
old = json.load(open(sys.argv[1])); new = json.load(open(sys.argv[2])); so, sn = sys.argv[3:5]
fo = set(json.load(open(f'{so}/fresh_files.json'))); fn = set(json.load(open(f'{sn}/fresh_files.json')))
lo = {r['row'] for r in json.load(open(f'{so}/LEDGER.json'))['rows'] if r['status'] == 'CLOSED'}; ln = {r['row'] for r in json.load(open(f'{sn}/LEDGER.json'))['rows'] if r['status'] == 'CLOSED'}
om, nm = old['modules'], new['modules']
d = dict(schema=1, target_established=False)
d['basis'] = dict(old=old['basis'], new=new['basis'], method_control='PCO_partition.py run at f7ccfbace7a with the ledger27/NNK_ files reproduces PRV_PARTITION.json exactly (module groups and subgroups, blob groups, rows 553/532/538, definition coverage counts); see PCO_CLASSIFICATIONS.json (control).')
idx = json.load(open(f'{sn}/lean_index.json')); p_of = {}
for g, v in idx.items(): p_of.setdefault(v['sha256'], v['paths'])
d['new_fresh_frozen_emission_files'] = sorted(fn - fo); d['new_fresh_frozen_emission_file_paths'] = {h: p_of.get(h, [])[:3] for h in sorted(fn - fo)}; d['removed_fresh_frozen_emission_files'] = sorted(fo - fn)
d['new_closed_rows'] = sorted(ln - lo); d['no_longer_closed_rows'] = sorted(lo - ln)
d['gate_modules_added_emitted'] = sorted(set(nm) - set(om)); d['gate_modules_removed_emitted'] = sorted(set(om) - set(nm))
ch = []
for m in sorted(set(om) & set(nm)):
    a, b = om[m], nm[m]
    reasons = []
    if a['subgroup'] != b['subgroup']: reasons.append('group')
    if a['coverage'] != b['coverage']: reasons.append('coverage')
    if a['prov'] != b['prov']: reasons.append('receipt_status')
    if a['n_rows'] != b['n_rows']: reasons.append('rows')
    if [c['sha256'] for c in a['candidates']] != [c['sha256'] for c in b['candidates']]: reasons.append('candidates')
    if not reasons: continue
    why = []
    if b.get('pilot_correction'): why.append('PILOT CORRECTION (not a base change): ' + b['pilot_correction']['reason'])
    if a['group'] == 'd' and b['group'] != 'd': why.append('module not reached by any CLOSED root at f7ccfbace7a, now reached (the 12 rows closed in ledger30 are instantiations over these modules)')
    if 'candidates' in reasons: why.append('import-matching candidate set changed (gate module recompiled from a different source or new committed copy)')
    if 'coverage' in reasons and 'candidates' not in reasons: why.append('reached definitions newly covered by a fresh receipted frozen emission merged after f7ccfbace7a, or reach set changed')
    if 'receipt_status' in reasons: why.append('a candidate gained or lost a receipt/pin hash')
    newr = sorted(set(b.get('rows', [])) & (ln - lo))
    if 'rows' in reasons and newr: why.append('newly CLOSED ledger30 rows reach the module: ' + ','.join(newr[:6]))
    ch.append(dict(module=m, old=dict(group=a['group'], subgroup=a['subgroup'], coverage=a['coverage'], rows=a['n_rows'], prov=a['prov']), new=dict(group=b['group'], subgroup=b['subgroup'], coverage=b['coverage'], rows=b['n_rows'], prov=b['prov']), changes=reasons, reason=' ; '.join(why) or 'see changes'))
d['module_changes'] = ch
d['module_regroups'] = [c for c in ch if 'group' in c['changes']]
d['summary_old'] = old['summary']; d['summary_new'] = new['summary']
so_, sn_ = old['summary']['rows'], new['summary']['rows']
d['impact_counts'] = dict(
    old=dict(closed=so_['closed'], rows_relying_on_group_c=so_['c'], rows_relying_on_c_or_b2_b3=so_['c_or_b_unlinked'], any_unreceipted_emitted_module=so_['any_unreceipted_emitted_module']),
    new=dict(closed=sn_['closed'], rows_relying_on_group_c=sn_['c'], rows_relying_on_c_or_b2_b3=sn_['c_or_b_unlinked'], c_or_b_or_a_pending=sn_['c_or_b_unlinked_or_a_pending'], any_unreceipted_emitted_module=sn_['any_unreceipted_emitted_module']),
    rows_added_to_group_c=sorted(set(new['rows_affected_c']) - set(old['rows_affected_c'])), rows_removed_from_group_c=sorted(set(old['rows_affected_c']) - set(new['rows_affected_c'])),
    rows_added_to_c_or_b=sorted(set(new['rows_affected_c_or_b_unlinked']) - set(old['rows_affected_c_or_b_unlinked'])), rows_removed_from_c_or_b=sorted(set(old['rows_affected_c_or_b_unlinked']) - set(new['rows_affected_c_or_b_unlinked'])))
json.dump(d, open(sys.argv[5], 'w'), indent=1); print(json.dumps(d['impact_counts'], indent=1)); print('regroups', len(d['module_regroups']), 'changes', len(ch), 'added', len(d['gate_modules_added_emitted']), 'removed', len(d['gate_modules_removed_emitted']))
