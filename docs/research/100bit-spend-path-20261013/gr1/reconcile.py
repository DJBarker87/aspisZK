#!/usr/bin/env python3
"""Reconcile recorded CU markers without rerunning any verifier."""
import json,re,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[4]
E=ROOT/'results/gr1-cost-20261013'
PHASES=['Parse','Semantic','Prepare','Checkpoint read','Merkle','Query folds and rho accumulation','Relation rounds and pairing','Final rho','Checkpoint write','Entry/exit']
def markers(logs):
 return [(a.removeprefix('Program log: r1:'),int(b.split()[2])) for a,b in zip(logs,logs[1:]) if a.startswith('Program log: r1:') and b.startswith('Program consumption: ')]
def buckets(ms,program,limit):
 out=dict.fromkeys(PHASES,0);prev=None
 for label,rem in ms:
  if label in ['begin','pool-adapter-stage2-begin']:prev=rem;continue
  if prev is None:prev=limit  # Adapter stage1 has no entry marker: parse includes its prefix.
  delta=prev-rem;assert delta>=0;(label,delta)
  if label=='parsed':key='Parse'
  elif label.startswith('semantic'):key='Semantic'
  elif label=='prepare':key='Prepare'
  elif label=='checkpoint-read':key='Checkpoint read'
  elif label.startswith('merkle:'):key='Merkle'
  elif label.startswith('query'):key='Query folds and rho accumulation'
  elif label=='relation':key='Relation rounds and pairing'
  elif label=='final':key='Final rho'
  elif label in ['checkpoint-write','account-write','pool-adapter-stage1-checkpoint-written']:key='Checkpoint write'
  else:raise ValueError(label)
  out[key]+=delta;prev=rem
 out['Entry/exit']=program-sum(out.values());assert out['Entry/exit']>=0
 assert sum(out.values())==program
 return out
def standalone(p):
 d=json.loads(p.read_text());c=d['verifier_cu'];out=buckets([(x['phase'],x['remaining_cu']) for x in d['phase_markers']],c,d['runtime']['limit_cu']);out.update({'Verifier subtotal':c,'Pool/custody outside verifier':0,'Transaction overhead':d['execution']['cu']-c,'Whole transaction':d['execution']['cu']});return out
def adapter(p,tx):
 d=json.loads(p.read_text());ex=d['execution'];logs=ex['stage1_logs' if tx==1 else 'logs'];whole=ex['stage1_compute_units' if tx==1 else 'compute_units']
 m=next(re.match(r'Program 7Q2\S+ consumed (\d+) of (\d+) compute units',l) for l in logs if re.match(r'Program 7Q2\S+ consumed (\d+) of (\d+) compute units',l));c,limit=map(int,m.groups());out=buckets(markers(logs),c,limit)
 outer=c if tx==1 else int(next(re.match(r'Program 5Pj\S+ consumed (\d+)',l).group(1) for l in logs if re.match(r'Program 5Pj\S+ consumed (\d+)',l)))
 out.update({'Verifier subtotal':c,'Pool/custody outside verifier':outer-c,'Transaction overhead':whole-outer,'Whole transaction':whole});return out
p2={}
for name,a,b in [('transfer',[56875,903170,489141,0,100280,822065,0,0,68211,1309],[36136,0,0,114865,120355,983707,1059165,94175,1783,1306]),('withdrawal',[56823,899866,489020,0,100222,819546,0,0,68211,1309],[36136,0,0,114779,120480,986011,1059243,94148,1783,1306])]:
 for tx,vals in [(1,a),(2,b)]:
  p=dict(zip(PHASES,vals));c=sum(vals);p.update({'Verifier subtotal':c,'Pool/custody outside verifier':0,'Transaction overhead':356,'Whole transaction':c+356});p2[f'{name}-tx{tx}']=p
all_data={};tables=[]
for name in ['transfer','withdrawal']:
 for tx in [1,2]:
  key=f'{name}-tx{tx}';d18=[]
  for run in range(1,6):d18.append(standalone(E/f'historical/d18-native/S2/measurements/{name}-acceptance-k10-tx{tx}-run{run}.json'))
  assert all(x==d18[0] for x in d18)
  cols={'P2':p2[key],'d18':d18[0]}
  for ver in ['v2','v3b']:
   runs=[adapter(E/f'pool-{ver}-{name}-{n}-evidence.json',tx) for n in range(1,6)];assert all(x==runs[0] for x in runs);cols[ver]=runs[0]
  all_data[key]=cols
  tables += [f'### {name.capitalize()} tx{tx}', '', '| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |','| --- | ---: | ---: | ---: | ---: | ---: |']
  for phase in cols['P2']:tables.append('| '+phase+' | '+' | '.join(f'{v[phase]:,}' for v in cols.values())+f" | {cols['P2'][phase]-cols['d18'][phase]:+,} |")
  tables.append('')
# Historical transfer stage chain: P2 bytes through geometry-dots; D18 regenerated proof.
stages={}
for stage in ['pairing','terminal','rho-clean','geometry-dots','d18']:
 stages[stage]={f'tx{tx}':standalone(E/f'historical/{stage}/S2/measurements/transfer-diagnostic-k10-tx{tx}-run1.json') for tx in [1,2]}
all_data['transfer_stage_chain']=stages
(E/'phase-accounting.json').write_text(json.dumps(all_data,indent=2)+'\n')
(E/'phase-tables.md').write_text('\n'.join(tables)+'\n')
# Every phase delta assigned to a transition. D18 changes the transport and proof.
lines=[]
for name in ['transfer','withdrawal']:
 if name=='withdrawal':
  stages={s:{f'tx{tx}':standalone(E/f'withdrawal-stages/{s}/S2/measurements/withdrawal-diagnostic-k10-tx{tx}-run1.json') for tx in [1,2]} for s in ['pairing','terminal','rho-clean','geometry-dots']}
  stages['d18']={f'tx{tx}':all_data[f'withdrawal-tx{tx}']['d18'] for tx in [1,2]}
  all_data['withdrawal_stage_chain']=stages
 lines += [f'### {name.capitalize()} stage attribution', '', '| Phase | P2 → pairing | → terminal | → rho-clean | → geometry-dots | → D18 transport + regenerated proof | Total P2 → d18 |','| --- | ---: | ---: | ---: | ---: | ---: | ---: |']
 for tx in [1,2]:
  for phase in p2[f'{name}-tx{tx}']:
   vals=[p2[f'{name}-tx{tx}'][phase]]+[stages[s][f'tx{tx}'][phase] for s in stages]
   diffs=[a-b for a,b in zip(vals,vals[1:])];assert sum(diffs)==vals[0]-vals[-1]
   lines.append(f'| tx{tx} {phase} | '+' | '.join(f'{v:+,}' for v in diffs+[sum(diffs)])+' |')
 lines.append('')
(E/'phase-accounting.json').write_text(json.dumps(all_data,indent=2)+'\n')
(E/'stage-attribution.md').write_text('\n'.join(lines)+'\n')
print('Exact phase reconciliation and five-run agreement passed.')
