#!/usr/bin/env python3
"""NPP_: summarise a stage-A log (JSON lines). Usage: python3 -I NPP_summarise_stageA.py <stdout.log>"""
import json, sys
from collections import Counter
rows = []
for l in open(sys.argv[1]):
    if l.startswith('{'):
        try: rows.append(json.loads(l))
        except Exception: pass
defs = [r for r in rows if r.get('k') == 'def' and 'status' not in r]
print(json.dumps({'def_copies': len(defs), 'def_equations': sum(1 for r in defs if r.get('eq')),
  'thm_copies': Counter(r.get('by') for r in rows if r.get('k') == 'thm' and 'by' in r),
  'status': Counter(r.get('status', '') for r in rows if 'status' in r),
  'sites_refined_in_new_copies': sum(r.get('sites', 0) for r in defs)}, indent=1))
for r in rows:
    if any(k in r for k in ('site_unrefined', 'choose_unrefined', 'dep_proof_untransported', 'eq_failed', 'compile_failed')) \
       or ('status' in r and r['status'].startswith('blocked (')):
        print(json.dumps(r, ensure_ascii=False)[:420])
for r in rows:
    if r.get('event') in ('stageA2', 'stageA'): print(json.dumps(r)[:300])
copies = [r for r in rows if 'copy' in r]
print('copies with IR:', sum(1 for r in copies if r.get('ir')), 'of', len(copies))
