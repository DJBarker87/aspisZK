#!/bin/bash
# PCXD_hm1.sh: normalise every *_HAND_MODELS.json of the campaign into one record list (scratch), before dedupe/classification.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6r/evidence
python3 -I -B - <<'PY'
import json, glob, re, sys, collections
sys.path.insert(0, 'prov-p6r-20261110')
import PCXD_lib as L
recs = []
def add(src, **k): recs.append(dict(source=src, **k))
def txt(x, n=1500):
    if x is None: return None
    if isinstance(x, str): return x[:n]
    if isinstance(x, dict): return (x.get('text') or x.get('note') or json.dumps(x))[:n]
    return json.dumps(x)[:n]
for f in sorted(glob.glob('prov-*/*HAND_MODELS.json')):
    job = f.split('/')[-1].replace('_HAND_MODELS.json', ''); o = json.load(open(f))
    es = o if isinstance(o, list) else o.get('entries')
    if es is None: continue
    for e in es:
        if not isinstance(e, dict): continue
        if job in ('PCQ_A', 'PCQC', 'PCQF', 'PCUC'):
            gh = e.get('gate_hits') or []
            add(job, gate_module=e.get('gate_module'), name=e.get('external_name'), gate_file=(gh[0]['file'] if gh else None), gate_text=(gh[0].get('text') if gh else None)[:1500] if gh and gh[0].get('text') else None,
                gate_form=e.get('gate_form'), fresh=txt(e.get('fresh_form')), crate=e.get('pinned_crate'), hand=e.get('hand_model'), origin=e.get('origin'), deps=e.get('dependent_reached_definitions'))
        elif job in ('PCUF', 'PCUE'):
            g = e.get('gate_definition')
            add(job, gate_module=e.get('gate_module'), name=e.get('external_name'), gate_file=(g or {}).get('file') if isinstance(g, dict) else None, gate_text=txt(g), aeneas_generated=(g or {}).get('aeneas_generated_text') if isinstance(g, dict) else None,
                fresh=e.get('fresh_axiom_text'), crate=e.get('pinned_crate'), hand=None, deps=e.get('proved_definitions_conditional_on_it'), by_name=e.get('resolved_to_gate_constant_by_name'), note=e.get('note'), has_gate=g is not None)
        elif job == 'PCUA':
            g = e.get('gate_definitions_found')
            add(job, gate_module=e.get('gate_module'), name=e.get('external_name'), gate_file=e.get('gate_file'), gate_text=txt(g), fresh=e.get('fresh_axiom_text'), crate=e.get('pinned_crate'), hand=None, by_name=e.get('resolved_to_gate_constant_by_name'), has_gate=bool(g), deps=e.get('dependent_reached_definitions_in_this_job'), note=e.get('note'))
        elif job in ('PCUB', 'PCUD'):
            add(job, gate_module=e.get('gate_module'), name=e.get('external_name'), gate_file=e.get('gate_file'), gate_text=txt(e.get('gate_definition')), fresh=txt(e.get('fresh_form')), crate=e.get('pinned_crate'), hand=e.get('resolved_as_hand_written_model'), origin=e.get('origin'), deps=e.get('dependent_reached_definitions'), has_gate=bool(e.get('gate_definition')))
        elif job == 'PCT':
            g = e.get('gate_definition')
            add(job, gate_module=e.get('gate_module'), name=e.get('external_name'), gate_file=(g or {}).get('file') if isinstance(g, dict) else None, gate_text=txt(g), fresh=txt(e.get('fresh_form')), crate=e.get('models_crate_and_version'), hand=None, classification=e.get('classification'), deps=e.get('reached_definitions_depending'), has_gate=bool(isinstance(g, dict) and g.get('text')))
        elif job == 'PCWA':
            g = e.get('gate_definition')
            add(job, gate_module=e.get('gate_module'), name=e.get('external_name'), gate_file=(g or {}).get('file'), gate_text=txt((g or {}).get('resolves_to') or g), fresh=txt(e.get('fresh_form')), crate=e.get('pinned_crate'), hand=True if e.get('kind') else None, kind=e.get('kind'), deps=e.get('dependent_reached_definitions'), has_gate=bool(g))
        elif job == 'PCVA':
            add(job, gate_module=e.get('where'), name=e.get('name'), gate_text=e.get('note'), has_gate=True, hand=True)
        elif job == 'PCWC' and 'external_funs' in e:
            for n in e['external_funs'] + e.get('external_types', []):
                add(job, gate_module=e['module'], name=n, note='external of fresh NJT-style emission resolved by name to the gate (P4c PCWC_HAND_MODELS)', has_gate=True)
        else: add(job, raw=str(e)[:300])
# PCQ_B / PCQE structured differently
for f in ('prov-p1b-20261109/PCQ_B_HAND_MODELS.json', 'prov-p1d-20261109/PCQE_HAND_MODELS.json'):
    o = json.load(open(f)); add(f.split('/')[-1][:-5], raw_summary=json.dumps({k: (v if not isinstance(v, (dict, list)) else (list(v)[:6])) for k, v in o.items()})[:1500])
json.dump(recs, open(L.SCR + '/hm_raw.json', 'w'))
c = collections.Counter(r['source'] for r in recs); print(len(recs), c)
print(collections.Counter((r['source'], bool(r.get('has_gate')), r.get('hand'), r.get('aeneas_generated')) for r in recs if 'gate_module' in r).most_common(30))
PY
