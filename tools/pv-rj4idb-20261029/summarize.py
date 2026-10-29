from pathlib import Path
import json,hashlib,re,subprocess
E=Path('evidence/pv-rj4idb-20261029');sha=lambda b:hashlib.sha256(b).hexdigest();runs=[]
for p in sorted(E.glob('modules-646*.json')):
 a=int(p.stem.split('-')[-1]);receipt=json.loads((E/f'receipt-{a}.json').read_text())
 for i,r in enumerate(json.loads(p.read_text())):
  assert sha((E/f'{a}-{i:02}.out').read_bytes())==r['output_sha256']
  assert sha((E/f'{a}-{i:02}.time').read_bytes())==r['time_sha256']
  runs.append(dict(attempt=a,module=r['module'],exit=r['exit'],wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=r['swaps'],source_revision=r['source_revision'],source_sha256=r['source_sha256'],dependencies=r['dependencies'],deps_fingerprint=r['deps_fingerprint'],accepted=r['accepted'],axioms=r['axioms']))
assert len(runs)==89 and len(set(x['attempt'] for x in runs))==89
assert all(x['swaps']==0 for x in runs)
assert all(64600<=x['attempt']<=64699 for x in runs)
allowed={'propext','Classical.choice','Quot.sound'}
for r in runs:
 if r['accepted']:
  for line in r['axioms']:
   m=re.search(r'\[([\s\S]*?)\]',line)
   if m:assert set(re.findall(r'[A-Za-z.]+',m[1]))<=allowed,line
receipts=[]
for p in E.glob('receipt-646*.json'):
 r=json.loads(p.read_text());ad=r.get('launch_admission',r.get('reservation'));assert ad['allowed'] is True,p
 receipts.append(r)
summary=dict(actual_Lean_attempts=len(runs),accepted_attempts=sum(x['accepted'] for x in runs),rejected_attempts=sum(not x['accepted'] for x in runs),preLean_empty_scope=dict(id=64600,exit=2,reason='own runner not staged; no Lean launched; ID retained consumed; original scope receipt retained'),native_scopes=2,Kani=0,VOID=0,refusals=len(list(E.glob('refusal-*.json'))),wall_seconds=sum(x['wall_seconds'] for x in runs),peak_rss_bytes=max(x['peak_rss_bytes'] for x in runs),swaps=0,accepted_axiom_sets='subsets of {propext, Classical.choice, Quot.sound}',audits={str(a):next(x for x in runs if x['attempt']==a) for a in [64697,64698,64699]},runs=runs)
(E/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# Exact per-target receipts','', 'Every accepted axioms query is standard-only. The rejected queries are not credited. Full revisions, SHA256, dependency fingerprints and original axiom lines are in summary.json and modules-646*.json.','','| ID | Target | Exit | Wall s | Peak RSS bytes | Swap | Source revision | Axioms |','|---|---|---:|---:|---:|---:|---|---|']
for r in runs:lines.append(f"| {r['attempt']} | `{r['module']}` | {r['exit']} | {r['wall_seconds']} | {r['peak_rss_bytes']} | {r['swaps']} | `{r['source_revision']}` | "+('standard only' if r['accepted'] else 'rejected; no credit')+' |')
(E/'receipts.md').write_text('\n'.join(lines)+'\n')
(E/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline','f63ed1bd4e..HEAD'],text=True))
print(json.dumps({k:v for k,v in summary.items() if k not in ['runs','audits']}))
