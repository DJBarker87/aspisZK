#!/usr/bin/env python3
"""UNPROVED P2: derive the cumulative table from recorded measurements."""
from pathlib import Path
import json
root=Path(__file__).resolve().parent.parent
out=root/'results/r1-precheck-20261010'
rows=['Parse','Semantic','Prepare','Checkpoint read','Merkle','Query folds and rho accumulation','Relation rounds and pairing','Final rho evaluation','Checkpoint write','Entry/exit and other overhead','Program subtotal CU','Other transaction overhead CU','Total transaction CU','Headroom to 1,300,000','Proof bytes','Checkpoint bytes','Peak heap bytes','Acceptance at 1,400,000']
columns=[];records=[]
for variant in ['S1','S2','D']:
    selection=out/variant/'balance-selection.json'
    k=json.loads(selection.read_text())['selected']['k'] if selection.exists() else None
    for tx in [1,2]:
        values={r:[] for r in rows}
        for fixture in ['transfer','withdrawal']:
            file=out/variant/'measurements'/f'{fixture}-diagnostic-k{k}-tx{tx}-run1.json'
            if not file.exists():
                for r in rows:values[r].append('pending')
                continue
            d=json.loads(file.read_text());assert d['verifier_completed']
            phases={r:0 for r in rows[:10]};markers=d['phase_markers'];prior=markers[0]['remaining_cu']
            for m in markers[1:]:
                label=m['phase'];cost=prior-m['remaining_cu'];prior=m['remaining_cu']
                key={'parsed':'Parse','semantic':'Semantic','prepare':'Prepare','checkpoint-read':'Checkpoint read','checkpoint-write':'Checkpoint write','account-write':'Checkpoint write','relation':'Relation rounds and pairing','final':'Final rho evaluation'}.get(label)
                if label.startswith('merkle:'):key='Merkle'
                if label.startswith('query:'):key='Query folds and rho accumulation'
                assert key,label
                phases[key]+=cost
            phases['Entry/exit and other overhead']=d['verifier_cu']-sum(phases.values())
            phases.update({'Program subtotal CU':d['verifier_cu'],'Other transaction overhead CU':d['execution']['cu']-d['verifier_cu'],'Total transaction CU':d['execution']['cu'],'Headroom to 1,300,000':1_300_000-d['execution']['cu'],'Proof bytes':d['proof_bytes'],'Checkpoint bytes':d['checkpoint_bytes'],'Peak heap bytes':d['sbf_heap_high_water_bytes']})
            attempts=list((out/variant/'measurements').glob(f'{fixture}-acceptance-k{k}-tx{tx}-run*.json'))
            phases['Acceptance at 1,400,000']=f"{sum(json.loads(p.read_text())['verifier_completed'] for p in attempts)}/{len(attempts)}"
            records.append(dict(variant=variant,fixture=fixture,transaction=tx,k=k,**phases))
            for row in rows:values[row].append(f'{phases[row]:,}' if isinstance(phases[row],int) else phases[row])
        columns.append((f'{variant} tx{tx}'+(f' (k={k})' if k is not None else ''),values))
table='| Phase / metric | '+' | '.join(c[0] for c in columns)+' |\n'
table+='| --- | '+' | '.join('---:' for _ in columns)+' |\n'
for row in rows:table+='| '+row+' | '+' | '.join(' / '.join(c[1][row]) for c in columns)+' |\n'
(out/'cumulative-table.md').write_text('UNPROVED R1 COST PROBE. Each cell is **transfer / withdrawal**; CU includes markers.\n\n'+table)
(out/'cumulative-table.json').write_text(json.dumps({'label':'UNPROVED COST PROBE','records':records},indent=2)+'\n')
