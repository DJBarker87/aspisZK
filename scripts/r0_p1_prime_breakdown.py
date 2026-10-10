#!/usr/bin/env python3
"""Partition B nested diagnostic intervals, keeping all unmarked CU explicit."""
import collections,json,sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=root/'results/r0-cost-probe-20261009'
base=json.loads((out/'c0-inherited.json').read_text())
records=[]
for fixture in ['transfer','withdrawal']:
    j=json.loads((out/'b-diagnostic'/f'{fixture}-diagnostic-1.json').read_text())
    assert j['verifier_completed'] and j['sbf_heap_high_water_bytes']<=262144
    markers=j['phase_markers'];coarse=[];stack=[];last=None;phase_parts=collections.Counter();event_counts=collections.Counter();fine_count=0;parts={};counts={};cals=[]
    for m in markers:
        label=m['phase'];remaining=m['remaining_cu']
        if label=='b:calibration':
            if last is not None and last[0]=='b:calibration': cals.append(last[1]-remaining)
            last=(label,remaining);continue
        if label=='begin': last=(label,remaining);coarse.append(m);continue
        if last is None: continue
        if label.startswith('b:'):
            kind=label[2];name=label[3:]
            assert kind in '+-',label
            phase_parts[stack[-1] if stack else 'unmarked']+=last[1]-remaining
            fine_count+=1
            if kind=='+': stack.append(name);event_counts[name]+=1
            else: assert stack.pop()==name,(label,stack)
        else:
            assert not stack,(label,stack)
            phase_parts['unmarked']+=last[1]-remaining
            elapsed=coarse[-1]['remaining_cu']-remaining
            assert sum(phase_parts.values())==elapsed
            parts[label]={'raw_cu':elapsed,'exclusive_intervals':dict(phase_parts),'fine_markers':fine_count,'interval_calls':dict(event_counts)}
            coarse.append(m);phase_parts.clear();event_counts.clear();fine_count=0
        last=(label,remaining)
    assert len(cals)==2 and cals[0]==cals[1],cals
    baseline=next(b for b in base['C0'] if b['variant']==fixture)
    comparison=[]
    for phase in ['semantic','chord-claims','merkle','v1','v2']:
        chosen=[p for name,p in parts.items() if name==phase or name.startswith(phase+':')]
        cu=sum(p['raw_cu'] for p in chosen);n=sum(p['fine_markers'] for p in chosen)
        comparison.append({'phase':phase,'S4_cu':baseline['phase_cu'][phase],'B_cu':cu,'delta_cu':cu-baseline['phase_cu'][phase],'fine_markers':n,'calibrated_marker_cu':n*cals[0],'residual_after_calibrated_markers_cu':cu-baseline['phase_cu'][phase]-n*cals[0]})
    records.append({'variant':fixture,'label':'COST PROBE: unproved; DIAGNOSTIC','verifier_cu':j['verifier_cu'],'heap_bytes':j['sbf_heap_high_water_bytes'],'calibration_cu':cals,'phase_partition_exact':True,'phases':parts,'S4_comparison':comparison})
result={'label':'COST PROBE: unproved','fixed_marker_cost_scope':'consecutive identical logging calls; call-site spills/control and compilation perturbations are NOT silently included','B':records}
p=out/'b-breakdown.json';assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n')
for r in records: print(json.dumps({k:r[k] for k in ['variant','verifier_cu','calibration_cu','S4_comparison']},indent=2))
